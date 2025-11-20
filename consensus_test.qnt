// -*- mode: Bluespec; -*-
// Tests for consensus_forks module with fork support

// ============================================================================
// MAIN MODULE WITH CONSTANTS
// ============================================================================

module consensus_main {
  import consensus(
    VALIDATORS = Set(1, 2, 3, 4),
    FAULTY = Set(4),
    F = 1,
    MAX_ROUND = 5,
    GENESIS_HASH = 0,
    GENESIS_ROUND = 0
  ).* from "./consensus"

  // ============================================================================
  // UNIT TESTS
  // ============================================================================

  // Test block type helpers with the record-based Block type
  run blockTypeTest = {
    val committedBlock: Block = {
      round: 3,
      hash: 30,
      parentHash: 20,
      isFork: false
    }
    val forkBlock: Block = {
      round: 3,
      hash: 31,
      parentHash: 20,
      isFork: true
    }
    all {
      assert(not(committedBlock.isFork)),
      assert(forkBlock.isFork),
      assert(committedBlock.round == 3),
      assert(forkBlock.round == 3),
      assert(committedBlock.parentHash == forkBlock.parentHash),
    }
  }

  // ============================================================================
  // SIMULATION RUNS
  // ============================================================================

  // Run with some forks to see ordering behavior
  run forkOrderingRun = {
    // Initialize with forks at rounds 2 and 3
    Init
    .then(validatorRevealsCommittedOrder(1, 0))
    .then(validatorRevealsCommittedOrder(2, 0))
    .then(validatorRevealsCommittedOrder(3, 0))
    // Quorum reached for round 0, now can reveal round 1
    .then(validatorRevealsCommittedOrder(1, 1))
    .then(validatorRevealsCommittedOrder(2, 1))
    .then(validatorRevealsCommittedOrder(3, 1))
    // Quorum reached for round 1, can reveal round 2 and forks
    .then(validatorRevealsCommittedOrder(1, 2))
    .then(validatorRevealsCommittedOrder(2, 2))
    // Validator 1 also reveals a fork at round 2 (if exists)
    .then(all {
      hasFork(2),
      validatorRevealsForkOrder(1, 2)
    })
    // Commits can only be for committed blocks
    .then(validatorRevealsCommit(1, 0))
    .then(validatorRevealsCommit(1, 1))
    // Check invariant: fork was ordered but cannot be committed
    .then(all {
      assert(forksNeverCommit),
      assert(commitRequiresOrdering),
      consensusState' = consensusState
    })
  }

  // Test that forks cannot be committed
  run forkCannotCommitTest = {
    Init
    // Reveal orderings
    .then(validatorRevealsCommittedOrder(1, 0))
    .then(validatorRevealsCommittedOrder(2, 0))
    .then(validatorRevealsCommittedOrder(3, 0))
    .then(validatorRevealsCommittedOrder(1, 1))
    .then(validatorRevealsCommittedOrder(2, 1))
    .then(validatorRevealsCommittedOrder(3, 1))
    // Commits
    .then(validatorRevealsCommit(1, 0))
    .then(validatorRevealsCommit(2, 0))
    .then(validatorRevealsCommit(3, 0))
    .then(validatorRevealsCommit(1, 1))
    // Verify invariant holds
    .then(all {
      assert(forksNeverCommit),
      consensusState' = consensusState
    })
  }

  // Test progressive ordering
  run progressiveOrderingTest = {
    Init
    // Genesis round - all validators
    .then(validatorRevealsCommittedOrder(1, 0))
    .then(validatorRevealsCommittedOrder(2, 0))
    .then(validatorRevealsCommittedOrder(3, 0))
    .then(validatorRevealsCommittedOrder(4, 0))
    // Round 1 - need quorum first
    .then(validatorRevealsCommittedOrder(1, 1))
    .then(validatorRevealsCommittedOrder(2, 1))
    .then(validatorRevealsCommittedOrder(3, 1))
    // Round 2
    .then(validatorRevealsCommittedOrder(1, 2))
    .then(validatorRevealsCommittedOrder(2, 2))
    .then(validatorRevealsCommittedOrder(3, 2))
    // Check state
    .then(all {
      assert(orderingsAtRound(0).size() == 4),
      assert(orderingsAtRound(1).size() == 3),
      assert(orderingsAtRound(2).size() == 3),
      consensusState' = consensusState
    })
  }
}
