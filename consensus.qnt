// -*- mode: Bluespec; -*-
// High-level specification of Aptos consensus behavior with fork support
// Models progressive disclosure: validators reveal orderings and commits
// Includes support for fork blocks that are ordered but never committed

module consensus {
  import basicSpells.* from "./spells/basicSpells"

  // ============================================================================
  // TYPES
  // ============================================================================

  type ValidatorId = int
  type Round = int
  type BlockHash = int

  // Block contains its identity and lineage
  type Block = {
    round: Round,
    hash: BlockHash,
    parentHash: BlockHash,
    isFork: bool
  }

  // ============================================================================
  // CONSTANTS
  // ============================================================================

  // Set of all validators (correct and faulty)
  const VALIDATORS: Set[ValidatorId]
  const FAULTY: Set[ValidatorId]

  // Number of faulty validators
  const F: int

  // Maximum round to model (for bounded model checking)
  const MAX_ROUND: int

  // Genesis block identifier
  const GENESIS_HASH: BlockHash
  const GENESIS_ROUND: Round

  // ============================================================================
  // DERIVED VALUES
  // ============================================================================

  // Quorum size (2F + 1 for BFT)
  val QUORUM: int = 2 * F + 1

  // All possible rounds
  pure def Rounds: Set[Round] = GENESIS_ROUND.to(MAX_ROUND)

  // Set of faulty validators
  val FaultyValidators: Set[ValidatorId] = FAULTY

  // ============================================================================
  // MESSAGE TYPES
  // ============================================================================

  // Ordering message revealed by a validator
  type Ordering = {
    validator: ValidatorId,
    block: Block
  }

  // Commit message revealed by a validator
  type Commit = {
    validator: ValidatorId,
    block: Block
  }

  // ============================================================================
  // STATE VARIABLES
  // ============================================================================

  // Consensus state - tracks what each validator has revealed
  type ConsensusState = {
    revealedOrderings: Set[Ordering],
    revealedCommits: Set[Commit],
    // All valid blocks indexed by hash
    blocks: BlockHash -> Block,
    // The committed chain: round -> block hash (for easy lookup)
    committedChain: Round -> BlockHash,
    // Fork blocks indexed by round (there can be one fork per round)
    forkBlocks: Round -> BlockHash
  }

  var consensusState: ConsensusState

  // ============================================================================
  // HELPER FUNCTIONS
  // ============================================================================

  // Get block by hash
  def getBlock(hash: BlockHash): Block = consensusState.blocks.get(hash)

  // Get committed block at round
  def getCommittedBlock(r: Round): Block = {
    val hash = consensusState.committedChain.get(r)
    consensusState.blocks.get(hash)
  }

  // Get fork block at round (if exists)
  def getForkBlock(r: Round): Block = {
    val hash = consensusState.forkBlocks.get(r)
    consensusState.blocks.get(hash)
  }

  // Check if a round has a fork
  def hasFork(r: Round): bool = consensusState.forkBlocks.keys().contains(r)

  // Get all valid blocks
  def allBlocks: Set[Block] = consensusState.blocks.keys().map(h => consensusState.blocks.get(h))

  // Check if validator has revealed ordering for a block
  def hasOrdering(v: ValidatorId, b: Block): bool =
    consensusState.revealedOrderings.exists(o => o.validator == v and o.block == b)

  // Check if validator has revealed commit for a block
  def hasCommit(v: ValidatorId, b: Block): bool =
    consensusState.revealedCommits.exists(c => c.validator == v and c.block == b)

  // Get orderings for a specific round (any block type)
  def orderingsAtRound(r: Round): Set[Ordering] =
    consensusState.revealedOrderings.filter(o => o.block.round == r)

  // Get commits for a specific round
  def commitsAtRound(r: Round): Set[Commit] =
    consensusState.revealedCommits.filter(c => c.block.round == r)

  // ============================================================================
  // INITIALIZATION
  // ============================================================================

  action Init: bool = {
    // Generate deterministic committed chain with parent links
    // Genesis block
    val genesisBlock: Block = {
      round: GENESIS_ROUND,
      hash: GENESIS_HASH,
      parentHash: GENESIS_HASH,  // Genesis is its own parent
      isFork: false
    }

    // Build committed chain: each block's parent is the previous block
    // Hash scheme: round r -> hash r * 10
    val committedBlocks: Round -> Block = Rounds.mapBy(r =>
      if (r == GENESIS_ROUND) genesisBlock
      else {
        round: r,
        hash: r * 10,
        parentHash: (r - 1) * 10,  // Parent is previous round's block
        isFork: false
      }
    )

    // Extract hash mapping for committed chain
    val committedHashes: Round -> BlockHash = Rounds.mapBy(r =>
      committedBlocks.get(r).hash
    )

    // Non-deterministically pick which rounds have forks (small subset, not genesis)
    nondet forkedRounds = oneOf(
      Rounds.exclude(Set(GENESIS_ROUND)).powerset().filter(s => s.size() <= 3)
    )

    // Generate fork blocks - each forks from the committed block at r-1
    // Hash scheme: fork at round r -> hash r * 10 + 1
    val forkBlocksList: Set[Block] = forkedRounds.map(r => {
      round: r,
      hash: r * 10 + 1,
      parentHash: (r - 1) * 10,  // Parent is committed block at r-1
      isFork: true
    })

    // Fork hash mapping
    val forkHashes: Round -> BlockHash = forkedRounds.mapBy(r => r * 10 + 1)

    // Combine all blocks into single set
    val allBlocksSet: Set[Block] =
      Rounds.map(r => committedBlocks.get(r)).union(forkBlocksList)

    // Create map from hash to block
    val allBlocksMap: BlockHash -> Block =
      allBlocksSet.map(b => b.hash).mapBy(h =>
        allBlocksSet.filter(b => b.hash == h).fold(genesisBlock, (acc, b) => b)
      )

    all {
      // Byzantine bound
      FAULTY.size() <= F,

      // Initialize consensus state
      consensusState' = {
        revealedOrderings: Set(),
        revealedCommits: Set(),
        blocks: allBlocksMap,
        committedChain: committedHashes,
        forkBlocks: forkHashes
      }
    }
  }

  action InitWithForks(forkRounds: Set[Round]): bool = {
    // Similar to Init, but with specified fork rounds
    // Genesis block
    val genesisBlock: Block = {
      round: GENESIS_ROUND,
      hash: GENESIS_HASH,
      parentHash: GENESIS_HASH,  // Genesis is its own parent
      isFork: false
    }

    // Build committed chain
    val committedBlocks: Round -> Block = Rounds.mapBy(r =>
      if (r == GENESIS_ROUND) genesisBlock
      else {
        round: r,
        hash: r * 10,
        parentHash: (r - 1) * 10,
        isFork: false
      }
    )

    val committedHashes: Round -> BlockHash = Rounds.mapBy(r =>
      committedBlocks.get(r).hash
    )

    // Generate fork blocks based on input
    val forkBlocksList: Set[Block] = forkRounds.map(r => {
      round: r,
      hash: r * 10 + 1,
      parentHash: (r - 1) * 10,
      isFork: true
    })

    val forkHashes: Round -> BlockHash = forkRounds.mapBy(r => r * 10 + 1)

    val allBlocksSet: Set[Block] =
      Rounds.map(r => committedBlocks.get(r)).union(forkBlocksList)

    val allBlocksMap: BlockHash -> Block =
      allBlocksSet.map(b => b.hash).mapBy(h =>
        allBlocksSet.filter(b => b.hash == h).fold(genesisBlock, (acc, b) => b)
      )

    all {
      consensusState' = {
        revealedOrderings: Set(),
        revealedCommits: Set(),
        blocks: allBlocksMap,
        committedChain: committedHashes,
        forkBlocks: forkHashes
      }
    }
  }

  // ============================================================================
  // PROGRESSIVE DISCLOSURE ACTIONS
  // ============================================================================

  // Validator reveals an ordering for a committed block
  action validatorRevealsCommittedOrder(v: ValidatorId, r: Round): bool = {
    val block = getCommittedBlock(r)
    all {
      // Round must be valid
      r >= GENESIS_ROUND,
      r <= MAX_ROUND,

      // Must have revealed ordering for parent first (causal ordering)
      // Genesis has no real parent requirement
      r == GENESIS_ROUND or {
        val parentBlock = getCommittedBlock(r - 1)
        hasOrdering(v, parentBlock)
      },

      // Quorum has revealed orderings for previous round
      r == GENESIS_ROUND or orderingsAtRound(r - 1).size() >= QUORUM,

      // Not already revealed by this validator
      not(hasOrdering(v, block)),

      // Reveal the ordering
      val ordering: Ordering = { validator: v, block: block }
      consensusState' = {
        ...consensusState,
        revealedOrderings: consensusState.revealedOrderings.union(Set(ordering))
      }
    }
  }

  // Validator reveals an ordering for a fork block
  action validatorRevealsForkOrder(v: ValidatorId, r: Round): bool = {
    all {
      // Round must have a fork
      hasFork(r),

      // Must have revealed ordering for parent first
      // Fork's parent is the committed block at r-1
      r > GENESIS_ROUND,

      // Quorum has revealed orderings for previous round
      orderingsAtRound(r - 1).size() >= QUORUM,

      // Get the fork block and check preconditions
      val block = getForkBlock(r)
      val parentBlock = getCommittedBlock(r - 1)
      all {
        // Must have revealed ordering for parent first
        hasOrdering(v, parentBlock),

        // Not already revealed by this validator
        not(hasOrdering(v, block)),

        // Reveal the ordering
        val ordering: Ordering = { validator: v, block: block }
        consensusState' = {
          ...consensusState,
          revealedOrderings: consensusState.revealedOrderings.union(Set(ordering))
        }
      }
    }
  }

  // Validator reveals a commit for a committed block
  // Note: Fork blocks can NEVER be committed
  action validatorRevealsCommit(v: ValidatorId, r: Round): bool = {
    val block = getCommittedBlock(r)
    all {
      // Round must be valid
      r >= GENESIS_ROUND,
      r <= MAX_ROUND,

      // Must have revealed commit for parent first (progression)
      r == GENESIS_ROUND or {
        val parentBlock = getCommittedBlock(r - 1)
        hasCommit(v, parentBlock)
      },

      // Must have revealed ordering for this block
      hasOrdering(v, block),

      // Not already revealed by this validator
      not(hasCommit(v, block)),

      // Reveal the commit
      val commit: Commit = { validator: v, block: block }
      consensusState' = {
        ...consensusState,
        revealedCommits: consensusState.revealedCommits.union(Set(commit))
      }
    }
  }

  action validatorRevealsOrder(v: ValidatorId, r: Round): bool = {
    any {
      validatorRevealsCommittedOrder(v, r),
      all {hasFork(r) , validatorRevealsForkOrder(v, r)}
    }
  }

  // Combined step action - non-deterministically choose an action
  action step: bool = {
    nondet v = oneOf(VALIDATORS)
    nondet r = oneOf(Rounds)
    any {
      validatorRevealsCommittedOrder(v, r),
      validatorRevealsForkOrder(v, r),
      validatorRevealsCommit(v, r)
    }
  }

  // ============================================================================
  // INVARIANTS
  // ============================================================================

  // Forks are never committed
  val forksNeverCommit: bool =
    consensusState.revealedCommits.forall(c => not(c.block.isFork))

  // Commits only happen after orderings
  val commitRequiresOrdering: bool =
    consensusState.revealedCommits.forall(c =>
      consensusState.revealedOrderings.exists(o =>
        o.validator == c.validator and o.block == c.block
      )
    )

  // All revealed orderings are for valid blocks
  val orderingsAreValid: bool =
    consensusState.revealedOrderings.forall(o =>
      consensusState.blocks.keys().contains(o.block.hash)
    )

  // Parent relationship is respected in orderings
  val parentOrderedFirst: bool =
    consensusState.revealedOrderings.forall(o =>
      o.block.round == GENESIS_ROUND or
      consensusState.revealedOrderings.exists(po =>
        po.validator == o.validator and po.block.hash == o.block.parentHash
      )
    )

  // ============================================================================
  // TEMPORAL PROPERTIES
  // ============================================================================

  // Orderings that will never have commits (the forks)
  def uncommittedOrderings: Set[Ordering] =
    consensusState.revealedOrderings.filter(o => o.block.isFork)

  // Count of fork orderings (for observability)
  def forkOrderingCount: int = uncommittedOrderings.size()
}
