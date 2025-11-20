// -*- mode: Bluespec; -*-
// Tests for consensus_observer module

module observer_test {
  import observer(
    VALIDATORS = Set(1, 2, 3, 4),
    FAULTY = Set(4),
    OBSERVERS = Set(5, 6, 7),
    F = 1,
    MAX_ROUND = 3,
    GENESIS_HASH = 0,
    GENESIS_ROUND = 0
  ).* from "./observer"

  // ============================================================================
  // UNIT TESTS
  // ============================================================================

  // Test basic quorum calculation
  run quorumTest = {
    initWithForks(Set())
    .then(validatorRevealsOrder(1, 0))
    .expect(QUORUM == 3 and VALIDATORS.size() == 4 and FAULTY.size() == 1)
  }

  // ============================================================================
  // SIMULATION RUNS - Progressive Disclosure
  // ============================================================================

  // Test basic validator ordering progression
  run basicOrderingTest = {
    initWithForks(Set())
    // Validators reveal orderings for genesis round
    .then(validatorRevealsOrder(1, 0))
    .then(validatorRevealsOrder(2, 0))
    .then(validatorRevealsOrder(3, 0))
    .expect(hasQuorumOrdered(0) and countValidatorsOrdered(0) == 3)
    // Now quorum reached, can reveal round 1
    .then(validatorRevealsOrder(1, 1))
    .then(validatorRevealsOrder(2, 1))
    .then(validatorRevealsOrder(3, 1))
    .expect(hasQuorumOrdered(1) and countValidatorsOrdered(1) == 3)
  }

  // Test observer receiving orderings after quorum
  run observerReceivesOrderingTest = {
    initWithForks(Set())
    // Build quorum for genesis
    .then(validatorRevealsOrder(1, 0))
    .then(validatorRevealsOrder(2, 0))
    .then(validatorRevealsOrder(3, 0))
    // Observer can now receive genesis ordering
    .then(observerReceivesOrdering(5, 0))
    // Build quorum for round 1
    .then(validatorRevealsOrder(1, 1))
    .then(validatorRevealsOrder(2, 1))
    .then(validatorRevealsOrder(3, 1))
    // Observer can receive round 1
    .then(observerReceivesOrdering(5, 1))
    .expect(observerState.observerReceived.get(5).size() == 2)
  }

  // Test observer committing after quorum commits
  run observerCommitsTest = {
    initWithForks(Set())
    // Build ordering quorum for genesis
    .then(validatorRevealsOrder(1, 0))
    .then(validatorRevealsOrder(2, 0))
    .then(validatorRevealsOrder(3, 0))
    // Observer receives genesis ordering
    .then(observerReceivesOrdering(5, 0))
    // Validators reveal commits for genesis
    .then(validatorRevealsCommit(1, 0))
    .then(validatorRevealsCommit(2, 0))
    .then(validatorRevealsCommit(3, 0))
    // Observer can now commit genesis
    .then(observerCommitsBlock(5, 0))
    .expect(
      observerState.observerCommitted.get(5).size() == 1 and
      getHighestCommitted(5) == 0
    )
  }

  // Test multiple rounds of ordering and committing
  run multiRoundCommitTest = {
    initWithForks(Set())
    // Round 0: order and commit
    .then(validatorRevealsOrder(1, 0))
    .then(validatorRevealsOrder(2, 0))
    .then(validatorRevealsOrder(3, 0))
    .then(observerReceivesOrdering(5, 0))
    .then(validatorRevealsCommit(1, 0))
    .then(validatorRevealsCommit(2, 0))
    .then(validatorRevealsCommit(3, 0))
    .then(observerCommitsBlock(5, 0))
    // Round 1: order and commit
    .then(validatorRevealsOrder(1, 1))
    .then(validatorRevealsOrder(2, 1))
    .then(validatorRevealsOrder(3, 1))
    .then(observerReceivesOrdering(5, 1))
    .then(validatorRevealsCommit(1, 1))
    .then(validatorRevealsCommit(2, 1))
    .then(validatorRevealsCommit(3, 1))
    .then(observerCommitsBlock(5, 1))
    // Round 2: order and commit
    .then(validatorRevealsOrder(1, 2))
    .then(validatorRevealsOrder(2, 2))
    .then(validatorRevealsOrder(3, 2))
    .then(observerReceivesOrdering(5, 2))
    .then(validatorRevealsCommit(1, 2))
    .then(validatorRevealsCommit(2, 2))
    .then(validatorRevealsCommit(3, 2))
    .then(observerCommitsBlock(5, 2))
    .expect(
      observerState.observerCommitted.get(5).size() == 3 and
      getHighestCommitted(5) == 2 and
      safetyInvariant
    )
  }

  // Test multiple observers
  run multipleObserversTest = {
    initWithForks(Set())
    // Build quorum for genesis
    .then(validatorRevealsOrder(1, 0))
    .then(validatorRevealsOrder(2, 0))
    .then(validatorRevealsOrder(3, 0))
    // Multiple observers receive
    .then(observerReceivesOrdering(5, 0))
    .then(observerReceivesOrdering(6, 0))
    .then(observerReceivesOrdering(7, 0))
    // Validators commit
    .then(validatorRevealsCommit(1, 0))
    .then(validatorRevealsCommit(2, 0))
    .then(validatorRevealsCommit(3, 0))
    // Multiple observers commit
    .then(observerCommitsBlock(5, 0))
    .then(observerCommitsBlock(6, 0))
    .then(observerCommitsBlock(7, 0))
    .expect(
      agreementInvariant and
      integrityInvariant and
      blockConsistencyInvariant
    )
  }

  // Test that observer cannot commit without receiving first
  run cannotCommitWithoutReceiveTest = {
    initWithForks(Set())
    // Build quorum for genesis
    .then(validatorRevealsOrder(1, 0))
    .then(validatorRevealsOrder(2, 0))
    .then(validatorRevealsOrder(3, 0))
    // Validators commit (but observer hasn't received)
    .then(validatorRevealsCommit(1, 0))
    .then(validatorRevealsCommit(2, 0))
    .then(validatorRevealsCommit(3, 0))
    // Observer 5 has not received or committed anything
    .expect(
      not(observerState.observerReceived.keys().contains(5)) and
      not(observerState.observerCommitted.keys().contains(5))
    )
  }

  // Test round monotonicity - commits must be in order
  run roundMonotonicityTest = {
    initWithForks(Set())
    // Setup rounds 0, 1, 2
    .then(validatorRevealsOrder(1, 0))
    .then(validatorRevealsOrder(2, 0))
    .then(validatorRevealsOrder(3, 0))
    .then(validatorRevealsOrder(1, 1))
    .then(validatorRevealsOrder(2, 1))
    .then(validatorRevealsOrder(3, 1))
    .then(validatorRevealsOrder(1, 2))
    .then(validatorRevealsOrder(2, 2))
    .then(validatorRevealsOrder(3, 2))
    // Observer receives all
    .then(observerReceivesOrdering(5, 0))
    .then(observerReceivesOrdering(5, 1))
    .then(observerReceivesOrdering(5, 2))
    // Validators commit all
    .then(validatorRevealsCommit(1, 0))
    .then(validatorRevealsCommit(2, 0))
    .then(validatorRevealsCommit(3, 0))
    .then(validatorRevealsCommit(1, 1))
    .then(validatorRevealsCommit(2, 1))
    .then(validatorRevealsCommit(3, 1))
    .then(validatorRevealsCommit(1, 2))
    .then(validatorRevealsCommit(2, 2))
    .then(validatorRevealsCommit(3, 2))
    // Observer commits in order
    .then(observerCommitsBlock(5, 0))
    .then(observerCommitsBlock(5, 1))
    .then(observerCommitsBlock(5, 2))
    .expect(
      roundMonotonicityInvariant and
      getHighestCommitted(5) == 2
    )
  }

  // Test that forks don't affect observer commits
  // Observer should only commit from committed chain, not forks
  // Initialize with a fork at round 1 to test fork safety
  run forkSafetyTest = {
    initWithForks(Set(1))
    // Build ordering quorum through rounds using committed blocks
    .then(validatorRevealsCommittedOrder(1, 0))
    .then(validatorRevealsCommittedOrder(2, 0))
    .then(validatorRevealsCommittedOrder(3, 0))
    .then(validatorRevealsCommittedOrder(1, 1))
    .then(validatorRevealsCommittedOrder(2, 1))
    .then(validatorRevealsCommittedOrder(3, 1))
    // Observer receives from committed chain
    .then(observerReceivesOrdering(5, 0))
    .then(observerReceivesOrdering(5, 1))
    // Validators commit
    .then(validatorRevealsCommit(1, 0))
    .then(validatorRevealsCommit(2, 0))
    .then(validatorRevealsCommit(3, 0))
    .then(validatorRevealsCommit(1, 1))
    .then(validatorRevealsCommit(2, 1))
    .then(validatorRevealsCommit(3, 1))
    // Observer commits
    .then(observerCommitsBlock(5, 0))
    .then(observerCommitsBlock(5, 1))
    .expect(
      blockConsistencyInvariant and
      safetyInvariant
    )
  }
}
