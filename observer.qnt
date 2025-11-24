// -*- mode: Bluespec; -*-
/**
 * Consensus Observer Model v2
 *
 * Simplified model focusing on observer logic:
 * - Single validator consensus (no quorum complexity)
 * - Observer processes consensus outputs with low-level logic
 * - Parent verification that can drop blocks (the bug)
 */

module observer {

  // ============================================================================
  // CONSTANTS
  // ============================================================================

  const MAX_ROUND: int
  const GENESIS_HASH: int
  const GENESIS_ROUND: int

  pure val Rounds: Set[int] = GENESIS_ROUND.to(MAX_ROUND)

  // ============================================================================
  // TYPES
  // ============================================================================

  type Round = int
  type BlockHash = int

  type Block = {
    round: Round,
    hash: BlockHash,
    parentHash: BlockHash,
    isFork: bool
  }

  // ============================================================================
  // STATE - Consensus Output
  // ============================================================================

  /// The committed chain (ground truth)
  var committedChain: Round -> Block

  /// Fork blocks (one possible fork per round)
  var forkBlocks: Round -> Block

  /// OrderedBlocks produced by consensus (observer can process these)
  var orderedOutputs: Set[(Round, BlockHash)]

  /// CommitDecisions produced by consensus (observer can process these)
  var commitOutputs: Set[(Round, BlockHash)]

  // ============================================================================
  // STATE - Observer
  // ============================================================================

  type ObserverState = {
    // OrderedBlocks the observer has processed (attempted)
    processedOrders: Set[(Round, BlockHash)],

    // Blocks that passed parent verification (the ordered chain)
    orderedChain: Set[(Round, BlockHash)],

    // Highest round in observer's ordered chain
    highestOrdered: Round,

    // CommitDecisions the observer has processed
    processedCommits: Set[(Round, BlockHash)],

    // Blocks the observer has committed
    committedBlocks: Set[(Round, BlockHash)],

    // Blocks dropped due to failed parent check (for analysis)
    droppedBlocks: Set[(Round, BlockHash)],
  }

  var observer: ObserverState

  // ============================================================================
  // HELPERS
  // ============================================================================

  /// Get committed block for a round
  def getCommittedBlock(r: Round): Block = committedChain.get(r)

  /// Get fork block for a round (if exists)
  def hasFork(r: Round): bool = forkBlocks.keys().contains(r)

  def getForkBlock(r: Round): Block = forkBlocks.get(r)

  /// Check if a block hash is from the committed chain
  def isCommittedBlock(r: Round, hash: BlockHash): bool =
    committedChain.get(r).hash == hash

  // ============================================================================
  // INITIALIZATION
  // ============================================================================

  action init: bool = {
    // Build committed chain
    val chain: Round -> Block = Rounds.mapBy(r =>
      if (r == GENESIS_ROUND) {
        { round: r, hash: GENESIS_HASH, parentHash: GENESIS_HASH, isFork: false }
      } else {
        { round: r, hash: r * 10, parentHash: (r - 1) * 10, isFork: false }
      }
    )

    all {
      committedChain' = chain,
      forkBlocks' = Map(),
      orderedOutputs' = Set(),
      commitOutputs' = Set(),
      observer' = {
        processedOrders: Set(),
        orderedChain: Set(),
        highestOrdered: GENESIS_ROUND - 1,
        processedCommits: Set(),
        committedBlocks: Set(),
        droppedBlocks: Set(),
      },
    }
  }

  /// Initialize with specific fork rounds
  action initWithForks(forkRounds: Set[Round]): bool = {
    // Build committed chain
    val chain: Round -> Block = Rounds.mapBy(r =>
      if (r == GENESIS_ROUND) {
        { round: r, hash: GENESIS_HASH, parentHash: GENESIS_HASH, isFork: false }
      } else {
        { round: r, hash: r * 10, parentHash: (r - 1) * 10, isFork: false }
      }
    )

    // Build fork blocks
    val forks: Round -> Block = forkRounds.mapBy(r =>
      { round: r, hash: r * 10 + 1, parentHash: (r - 1) * 10, isFork: true }
    )

    all {
      committedChain' = chain,
      forkBlocks' = forks,
      orderedOutputs' = Set(),
      commitOutputs' = Set(),
      observer' = {
        processedOrders: Set(),
        orderedChain: Set(),
        highestOrdered: GENESIS_ROUND - 1,
        processedCommits: Set(),
        committedBlocks: Set(),
        droppedBlocks: Set(),
      },
    }
  }

  // ============================================================================
  // CONSENSUS ACTIONS - Produce outputs
  // ============================================================================

  /// Consensus orders a committed block
  action consensusOrdersCommitted(r: Round): bool = {
    val block = getCommittedBlock(r)
    all {
      Rounds.contains(r),
      // Not already ordered
      not(orderedOutputs.contains((r, block.hash))),

      orderedOutputs' = orderedOutputs.union(Set((r, block.hash))),
      commitOutputs' = commitOutputs,
      committedChain' = committedChain,
      forkBlocks' = forkBlocks,
      observer' = observer,
    }
  }

  /// Consensus orders a fork block
  action consensusOrdersFork(r: Round): bool = {
    all {
      hasFork(r),
      val block = getForkBlock(r)
      all {
        // Not already ordered
        not(orderedOutputs.contains((r, block.hash))),

        orderedOutputs' = orderedOutputs.union(Set((r, block.hash))),
        commitOutputs' = commitOutputs,
        committedChain' = committedChain,
        forkBlocks' = forkBlocks,
        observer' = observer,
      }
    }
  }

  /// Consensus commits a block (only committed chain, not forks)
  action consensusCommits(r: Round): bool = {
    val block = getCommittedBlock(r)
    all {
      Rounds.contains(r),
      // Must have ordered this block first
      orderedOutputs.contains((r, block.hash)),
      // Not already committed
      not(commitOutputs.contains((r, block.hash))),

      commitOutputs' = commitOutputs.union(Set((r, block.hash))),
      orderedOutputs' = orderedOutputs,
      committedChain' = committedChain,
      forkBlocks' = forkBlocks,
      observer' = observer,
    }
  }

  // ============================================================================
  // OBSERVER ACTIONS - Process outputs
  // ============================================================================

  /// Observer processes an OrderedBlock from consensus
  /// This is where parent verification happens (and can drop blocks)
  action observerProcessesOrder(r: Round, hash: BlockHash): bool = {
    all {
      // Must be in consensus output
      orderedOutputs.contains((r, hash)),
      // Must not be already processed
      not(observer.processedOrders.contains((r, hash))),

      // Parent verification
      val parentOk = if (r == GENESIS_ROUND) {
        true
      } else {
        // Parent must be the previous round AND already in observer's ordered chain
        r == observer.highestOrdered + 1
      }

      // Mark as processed
      val newProcessed = observer.processedOrders.union(Set((r, hash)))

      if (parentOk) {
        // SUCCESS: add to ordered chain
        observer' = {
          ...observer,
          processedOrders: newProcessed,
          orderedChain: observer.orderedChain.union(Set((r, hash))),
          highestOrdered: r,
        }
      } else {
        // FAIL: drop the block - THE BUG
        observer' = {
          ...observer,
          processedOrders: newProcessed,
          droppedBlocks: observer.droppedBlocks.union(Set((r, hash))),
        }
      },

      // Consensus state unchanged
      orderedOutputs' = orderedOutputs,
      commitOutputs' = commitOutputs,
      committedChain' = committedChain,
      forkBlocks' = forkBlocks,
    }
  }

  /// Observer processes a CommitDecision from consensus
  action observerProcessesCommit(r: Round, hash: BlockHash): bool = {
    all {
      // Must be in consensus commit output
      commitOutputs.contains((r, hash)),
      // Must not be already processed
      not(observer.processedCommits.contains((r, hash))),
      // Block must be in observer's ordered chain
      observer.orderedChain.contains((r, hash)),

      observer' = {
        ...observer,
        processedCommits: observer.processedCommits.union(Set((r, hash))),
        committedBlocks: observer.committedBlocks.union(Set((r, hash))),
      },

      // Consensus state unchanged
      orderedOutputs' = orderedOutputs,
      commitOutputs' = commitOutputs,
      committedChain' = committedChain,
      forkBlocks' = forkBlocks,
    }
  }

  // ============================================================================
  // INVARIANTS
  // ============================================================================

  /// Safety: Observer only commits blocks from committed chain
  val commitIntegrity: bool =
    observer.committedBlocks.forall(entry =>
      isCommittedBlock(entry._1, entry._2)
    )

  /// Safety: Observer's ordered chain only has committed blocks
  val orderIntegrity: bool =
    observer.orderedChain.forall(entry =>
      isCommittedBlock(entry._1, entry._2)
    )

  /// Liveness: No blocks should be dropped
  val noBlocksDropped: bool =
    observer.droppedBlocks.size() == 0

  /// All processed orders are either in chain or dropped
  val processingComplete: bool =
    observer.processedOrders.forall(entry =>
      observer.orderedChain.contains(entry) or observer.droppedBlocks.contains(entry)
    )

  val safetyInvariant: bool = all {
    commitIntegrity,
    processingComplete,
  }

  // ============================================================================
  // STATE MACHINE
  // ============================================================================

  action step: bool = any {
    // Consensus produces outputs
    nondet r = Rounds.oneOf()
    any {
      consensusOrdersCommitted(r),
      consensusOrdersFork(r),
      consensusCommits(r),
    },

    // Observer processes outputs
    nondet r = Rounds.oneOf()
    nondet hash = Set(r * 10, r * 10 + 1).oneOf()  // committed or fork hash
    any {
      observerProcessesOrder(r, hash),
      observerProcessesCommit(r, hash),
    },
  }
}
