// -*- mode: Bluespec; -*-
/**
 * Aptos Consensus Observer Protocol Specification (AIP-93)
 *
 * This specification models the observer component of Aptos Consensus Observer.
 * The consensus protocol (AptosBFT) is treated as a black box that produces
 * certified blocks with quorum certificates.
 *
 * ============================================================================
 * PRIMARY SOURCES
 * ============================================================================
 * [AIP-93] https://github.com/aptos-foundation/AIPs/blob/main/aips/aip-93.md
 *          Official Aptos Improvement Proposal for Consensus Observer
 * [DOCS]   https://aptos.dev/en/network/nodes/configure/consensus-observer
 *          Aptos official documentation
 * [BLOG]   https://medium.com/aptoslabs/ultra-low-latency-block-synchronization-at-high-tps-consensus-observer-aip-93-f8d53fb714f0
 *          Technical blog post (access restricted)
 *
 * ============================================================================
 * KEY DESIGN DECISIONS (with source references)
 * ============================================================================
 *
 * 1. BLACK BOX CONSENSUS ([AIP-93] Section: Solution Architecture)
 *    Quote: "validators propose and order blocks via consensus, they simultaneously
 *    broadcast to validator fullnodes (VFNs)"
 *    => We model validators as publishers that produce certified blocks, not the
 *       consensus mechanism itself
 *
 * 2. PARALLEL PROCESSING ([AIP-93] Section: Protocol Details)
 *    Quote: "Validators and fullnodes execute blocks concurrently, without waiting
 *    for completion"
 *    => Observers can receive, verify, and execute blocks independently
 *
 * 3. THREE MESSAGE TYPES ([AIP-93] Section: Network Messages)
 *    - Ordered Block: "epoch, round number, block hash, and quorum signatures"
 *    - Block Payload: "Raw transaction data corresponding to ordered block identifiers"
 *    - Committed Block: "Committed block data with quorum signatures over results"
 *    => We model OrderedMsg and CommitMsg (payload abstracted)
 *
 * 4. VERIFICATION PROCESS ([AIP-93] Section: Verification Process)
 *    Observers validate:
 *    - "Block well-formedness"
 *    - "Correct block chaining"
 *    - "Transaction validity"
 *    - "Quorum signature authenticity"
 *    => We model QC verification with quorum threshold checks
 *
 * 5. BYZANTINE FAULT TOLERANCE (Standard BFT assumption)
 *    Quote: "quorum certificate (QC) signatures" require >= 2f+1 validators
 *    => QUORUM = 2F + 1, where F is Byzantine threshold
 */

module observer {
  import basicSpells.* from "./spells/basicSpells"

  // ============================================================================
  // SYSTEM PARAMETERS
  // ============================================================================

  // Constants to be provided by instantiation
  const VALIDATORS: Set[int]
  const FAULTY: Set[int]
  const OBSERVERS: Set[int]
  const F: int
  const MAX_ROUND: int
  const GENESIS_HASH: int
  const GENESIS_ROUND: int

  // Derived constant
  val QUORUM: int = 2 * F + 1

  // ============================================================================
  // IMPORT CONSENSUS MODULE
  // The consensus module provides progressive disclosure of orderings/commits
  // We import specific items to avoid name conflicts
  // ============================================================================

  import consensus(
    VALIDATORS = VALIDATORS,
    FAULTY = FAULTY,
    F = F,
    MAX_ROUND = MAX_ROUND,
    GENESIS_HASH = GENESIS_HASH,
    GENESIS_ROUND = GENESIS_ROUND
  ) as cons from "./consensus"

  // Re-export types from consensus module for local use
  type ValidatorId = int
  type ObserverId = int
  type Round = int
  type BlockHash = int

  // ============================================================================
  // STATE VARIABLES
  // ============================================================================

  /// Observer state (indexed by observer ID)
  /// Observers directly query the consensus module's revealed orderings/commits
  type ObserverState = {
    observerReceived: ObserverId -> Set[(Round, BlockHash)],
    observerCommitted: ObserverId -> Set[(Round, BlockHash)],
    observerHighestCommitted: ObserverId -> Round,
  }

  // Note: consensusState comes from the imported consensus module

  var observerState: ObserverState

  // ============================================================================
  // HELPER FUNCTIONS
  // ============================================================================

  pure def isObserver(n: int): bool = OBSERVERS.contains(n)

  // ============================================================================
  // MAP UTILITIES (using basicSpells)
  // ============================================================================

  /// Add entry to a map of sets (using spells)
  pure def addToMapSet(m: a -> Set[b], k: a, entry: b): a -> Set[b] = {
    setByWithDefault(m, k, s => setAdd(s, entry), Set())
  }

  // ============================================================================
  // DOMAIN-SPECIFIC UTILITIES
  // ============================================================================

  /// Get highest committed round for an observer (or genesis if none)
  def getHighestCommitted(obs: ObserverId): Round =
    observerState.observerHighestCommitted.getOrElse(obs, GENESIS_ROUND)

  /// Count validators who have revealed orderings for a specific round
  def countValidatorsOrdered(r: Round): int =
    cons::consensusState.revealedOrderings.filter(o => o.block.round == r).size()

  /// Count validators who have revealed commits for a specific (round, block) pair
  def countValidatorsCommitted(r: Round, b: BlockHash): int =
    cons::consensusState.revealedCommits.filter(c =>
      c.block.round == r and c.block.hash == b
    ).size()

  /// Check if a quorum of validators has ordered a round
  def hasQuorumOrdered(r: Round): bool =
    countValidatorsOrdered(r) >= QUORUM

  /// Check if a quorum of validators has committed a (round, block) pair
  def hasQuorumCommitted(r: Round, b: BlockHash): bool =
    countValidatorsCommitted(r, b) >= QUORUM

  /// Get the committed block hash for a round
  def getBlockForRound(r: Round): BlockHash =
    cons::consensusState.committedChain.get(r)

  // ============================================================================
  // CONSENSUS ACTIONS (Validators reveal orderings/commits)
  // ============================================================================

  /// Validator reveals an ordering for a round (may be committed or fork)
  /// Directly uses the consensus module's action
  action validatorRevealsOrder(v: ValidatorId, r: Round): bool = all {
    cons::validatorRevealsOrder(v, r),
    observerState' = observerState,
  }

  /// Validator reveals an ordering specifically for committed block (not fork)
  /// Use this in tests when you need deterministic committed block ordering
  action validatorRevealsCommittedOrder(v: ValidatorId, r: Round): bool = all {
    cons::validatorRevealsCommittedOrder(v, r),
    observerState' = observerState,
  }

  /// Validator reveals a commit for a round
  /// Directly uses the consensus module's action
  action validatorRevealsCommit(v: ValidatorId, r: Round): bool = all {
    cons::validatorRevealsCommit(v, r),
    observerState' = observerState,
  }

  // ============================================================================
  // OBSERVER ACTIONS
  // Observers directly query the consensus module's revealed state
  // ============================================================================

  /// Observer receives an ordering for a round
  /// Requires quorum of validators to have revealed orderings for this round
  action observerReceivesOrdering(obs: ObserverId, r: Round): bool = {
    val block = getBlockForRound(r)

    all {
      isObserver(obs),
      // QC verification: quorum of validators must have ordered this round
      hasQuorumOrdered(r),
      // Not already received
      not(observerState.observerReceived.keys().contains(obs) and
          observerState.observerReceived.get(obs).contains((r, block))),

      // Consensus state unchanged
      cons::consensusState' = cons::consensusState,

      observerState' = {
        ...observerState,
        observerReceived: addToMapSet(observerState.observerReceived, obs, (r, block)),
      },
    }
  }

  /// Observer commits a block for a round
  /// Requires quorum of validators to have revealed commits for this round
  action observerCommitsBlock(obs: ObserverId, r: Round): bool = {
    val block = getBlockForRound(r)

    all {
      isObserver(obs),
      // Must have received this block first
      observerState.observerReceived.keys().contains(obs),
      observerState.observerReceived.get(obs).contains((r, block)),
      // QC verification: quorum of validators must have committed this round
      hasQuorumCommitted(r, block),
      // Round must be higher than highest committed (or first commit)
      not(observerState.observerHighestCommitted.keys().contains(obs)) or
        r > getHighestCommitted(obs),
      // Not already committed
      not(observerState.observerCommitted.keys().contains(obs) and
          observerState.observerCommitted.get(obs).contains((r, block))),

      // Consensus state unchanged
      cons::consensusState' = cons::consensusState,

      observerState' = {
        ...observerState,
        observerCommitted: addToMapSet(observerState.observerCommitted, obs, (r, block)),
        observerHighestCommitted: observerState.observerHighestCommitted.put(obs, r),
      },
    }
  }

  // ============================================================================
  // SAFETY INVARIANTS
  // ============================================================================

  /// SAFETY 1: Agreement
  /// Two observers never commit different blocks for the same round
  val agreementInvariant: bool =
    OBSERVERS.forall(obs1 =>
      OBSERVERS.forall(obs2 =>
        observerState.observerCommitted.keys().contains(obs1) and
        observerState.observerCommitted.keys().contains(obs2) implies
          observerState.observerCommitted.get(obs1).forall(entry1 =>
            observerState.observerCommitted.get(obs2).forall(entry2 =>
              (entry1._1 == entry2._1) implies (entry1._2 == entry2._2)
            )
          )
      )
    )

  /// SAFETY 2: Integrity
  /// Observers only commit blocks that a quorum actually committed
  /// Uses the consensus module's revealedCommits
  val integrityInvariant: bool =
    observerState.observerCommitted.keys().forall(obs =>
      observerState.observerCommitted.get(obs).forall(entry => {
        val round = entry._1
        val blockHash = entry._2
        // Count validators who have revealed commits for this (round, block)
        val committedValidators = cons::consensusState.revealedCommits.filter(c =>
          c.block.round == round and c.block.hash == blockHash
        )
        committedValidators.size() >= QUORUM
      })
    )

  /// SAFETY 3: Block consistency with committed chain
  /// All committed blocks must match the committed chain (not forks)
  val blockConsistencyInvariant: bool =
    observerState.observerCommitted.keys().forall(obs =>
      observerState.observerCommitted.get(obs).forall(entry => {
        val round = entry._1
        val blockHash = entry._2
        // Block must match what's in the committed chain
        cons::consensusState.committedChain.get(round) == blockHash
      })
    )

  /// SAFETY 4: Round monotonicity
  /// Observers commit rounds in strictly increasing order
  val roundMonotonicityInvariant: bool =
    observerState.observerCommitted.keys().forall(obs => {
      val committedEntries = observerState.observerCommitted.get(obs)
      // All rounds for this observer must be unique
      committedEntries.forall(entry1 =>
        committedEntries.forall(entry2 =>
          (entry1._1 == entry2._1) implies (entry1 == entry2)
        )
      )
    }) and
    // Additionally: highest committed round must match actual highest
    observerState.observerHighestCommitted.keys().forall(obs => {
      val highestRound = observerState.observerHighestCommitted.get(obs)
      // All committed rounds for this observer must be <= highest
      observerState.observerCommitted.keys().contains(obs) implies
        observerState.observerCommitted.get(obs).forall(entry => entry._1 <= highestRound)
    })

  /// Combined safety invariant
  val safetyInvariant: bool = all {
    agreementInvariant,
    integrityInvariant,
    blockConsistencyInvariant,
    roundMonotonicityInvariant,
  }

  // ============================================================================
  // STATE MACHINE
  // ============================================================================

  action init = {
    all {
      // Initialize consensus module state (includes non-deterministic fork generation)
      cons::Init,

      // Initialize observer state
      observerState' = {
        observerReceived: Map(),
        observerCommitted: Map(),
        observerHighestCommitted: Map(),
      },
    }
  }

  action initWithForks(forkRounds: Set[Round]): bool = {
    all {
      // Initialize consensus module state with specified forks
      cons::InitWithForks(forkRounds),

      // Initialize observer state
      observerState' = {
        observerReceived: Map(),
        observerCommitted: Map(),
        observerHighestCommitted: Map(),
      },
    }
  }

  

  action step = any {
    // Validator actions (progressive disclosure from consensus module)
    all {
      nondet v = VALIDATORS.oneOf()
      nondet r = cons::Rounds.oneOf()
      validatorRevealsOrder(v, r)
    },
    all {
      nondet v = VALIDATORS.oneOf()
      nondet r = cons::Rounds.oneOf()
      validatorRevealsCommit(v, r)
    },

    // Observer actions (directly query consensus state)
    all {
      nondet obs = OBSERVERS.oneOf()
      nondet r = cons::Rounds.oneOf()
      observerReceivesOrdering(obs, r)
    },
    all {
      nondet obs = OBSERVERS.oneOf()
      nondet r = cons::Rounds.oneOf()
      observerCommitsBlock(obs, r)
    },
  }
}
