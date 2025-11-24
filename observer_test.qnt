// -*- mode: Bluespec; -*-
// Tests for observer_v2 - demonstrating parent verification bug

module observer_test{
  import observer(
    MAX_ROUND = 4,
    GENESIS_HASH = 0,
    GENESIS_ROUND = 0
  ).* from "./observer"

  // ============================================================================
  // BUG DEMONSTRATION: Out-of-Order Processing
  // ============================================================================

  /// Block 2 is processed before block 1 -> gets dropped
  run outOfOrderDropTest = {
    initWithForks(Set())
    // Consensus orders rounds 0, 1, 2
    .then(consensusOrdersCommitted(0))
    .then(consensusOrdersCommitted(1))
    .then(consensusOrdersCommitted(2))

    // Observer processes out of order
    .then(observerProcessesOrder(2, 20))  // DROPPED - parent (round 1) not in chain
    .then(observerProcessesOrder(0, 0))   // OK - genesis
    .then(observerProcessesOrder(1, 10))  // OK - parent is round 0

    // Round 2 was dropped
    .expect(
      observer.droppedBlocks.contains((2, 20)) and
      observer.orderedChain.contains((0, 0)) and
      observer.orderedChain.contains((1, 10)) and
      not(observer.orderedChain.contains((2, 20))) and
      not(noBlocksDropped)
    )
  }

  /// Worst case: reverse order processing drops everything except genesis
  run reverseOrderDropTest = {
    initWithForks(Set())
    .then(consensusOrdersCommitted(0))
    .then(consensusOrdersCommitted(1))
    .then(consensusOrdersCommitted(2))
    .then(consensusOrdersCommitted(3))

    // Process in reverse order
    .then(observerProcessesOrder(3, 30))  // DROPPED
    .then(observerProcessesOrder(2, 20))  // DROPPED
    .then(observerProcessesOrder(1, 10))  // DROPPED
    .then(observerProcessesOrder(0, 0))   // OK

    // Only genesis in chain, rest dropped
    .expect(
      observer.orderedChain.size() == 1 and
      observer.droppedBlocks.size() == 3
    )
  }

  // ============================================================================
  // CORRECT BEHAVIOR: In-Order Processing
  // ============================================================================

  /// When processed in order, everything works
  run inOrderTest = {
    initWithForks(Set())
    .then(consensusOrdersCommitted(0))
    .then(consensusOrdersCommitted(1))
    .then(consensusOrdersCommitted(2))

    // Process in order
    .then(observerProcessesOrder(0, 0))
    .then(observerProcessesOrder(1, 10))
    .then(observerProcessesOrder(2, 20))

    .expect(
      observer.orderedChain.size() == 3 and
      observer.droppedBlocks.size() == 0 and
      noBlocksDropped
    )
  }

  // ============================================================================
  // ORDER/COMMIT INTERPLAY
  // ============================================================================

  /// Full flow: order then commit
  run orderThenCommitTest = {
    initWithForks(Set())
    .then(consensusOrdersCommitted(0))
    .then(consensusOrdersCommitted(1))
    .then(consensusCommits(0))
    .then(consensusCommits(1))

    // Observer processes orders
    .then(observerProcessesOrder(0, 0))
    .then(observerProcessesOrder(1, 10))

    // Observer processes commits
    .then(observerProcessesCommit(0, 0))
    .then(observerProcessesCommit(1, 10))

    .expect(
      observer.committedBlocks.size() == 2 and
      safetyInvariant
    )
  }

  /// Commit arrives but block not in ordered chain (due to drop)
  run commitWithoutOrderedBlockTest = {
    initWithForks(Set())
    .then(consensusOrdersCommitted(0))
    .then(consensusOrdersCommitted(1))
    .then(consensusCommits(0))
    .then(consensusCommits(1))

    // Observer processes round 1 first (gets dropped)
    .then(observerProcessesOrder(1, 10))  // DROPPED
    .then(observerProcessesOrder(0, 0))   // OK

    // Can commit round 0
    .then(observerProcessesCommit(0, 0))

    // Cannot commit round 1 - it's not in ordered chain
    // (observerProcessesCommit(1, 10) would fail precondition)
    .expect(
      observer.committedBlocks.contains((0, 0)) and
      not(observer.orderedChain.contains((1, 10))) and
      observer.droppedBlocks.contains((1, 10))
    )
  }

  // ============================================================================
  // FORK HANDLING
  // ============================================================================

  /// Observer can receive fork blocks but shouldn't commit them
  run forkBlockTest = {
    initWithForks(Set(1))  // Fork at round 1
    .then(consensusOrdersCommitted(0))
    .then(consensusOrdersFork(1))  // Fork block ordered
    .then(consensusOrdersCommitted(1))  // Committed block also ordered

    // Observer processes in order
    .then(observerProcessesOrder(0, 0))

    // Observer processes fork block for round 1
    .then(observerProcessesOrder(1, 11))  // Fork hash = 1*10+1 = 11

    // Fork is in ordered chain (passed parent check)
    .expect(
      observer.orderedChain.contains((1, 11)) and
      // But it's a fork, not from committed chain
      not(isCommittedBlock(1, 11))
    )
  }

  /// Fork block should not be committable (consensus doesn't commit forks)
  run forkNotCommittableTest = {
    initWithForks(Set(1))
    .then(consensusOrdersCommitted(0))
    .then(consensusOrdersFork(1))
    .then(consensusOrdersCommitted(1))
    .then(consensusCommits(0))
    // consensus cannot commit fork (only committed block)
    .then(consensusCommits(1))

    .then(observerProcessesOrder(0, 0))
    .then(observerProcessesOrder(1, 11))  // Process fork

    // Commit for round 1 is for hash 10 (committed), not 11 (fork)
    // Observer has fork in chain, so can't process commit for committed block
    .expect(
      observer.orderedChain.contains((1, 11)) and
      commitOutputs.contains((1, 10)) and
      // Can't commit because observer has wrong block in chain
      not(observer.orderedChain.contains((1, 10)))
    )
  }

  // ============================================================================
  // GAP SCENARIOS
  // ============================================================================

  /// Gap in processing: rounds 0, 2 processed, round 1 skipped
  run gapInProcessingTest = {
    initWithForks(Set())
    .then(consensusOrdersCommitted(0))
    .then(consensusOrdersCommitted(1))
    .then(consensusOrdersCommitted(2))

    // Skip round 1
    .then(observerProcessesOrder(0, 0))
    .then(observerProcessesOrder(2, 20))  // DROPPED - parent is round 1, not in chain

    .expect(
      observer.orderedChain.size() == 1 and
      observer.droppedBlocks.contains((2, 20))
    )
  }

  /// After gap, later blocks can still be processed if in order
  run recoveryAfterGapTest = {
    initWithForks(Set())
    .then(consensusOrdersCommitted(0))
    .then(consensusOrdersCommitted(1))
    .then(consensusOrdersCommitted(2))
    .then(consensusOrdersCommitted(3))

    // Process 0, skip 1, process 2 (dropped), then process 1 and 3
    .then(observerProcessesOrder(0, 0))   // OK
    .then(observerProcessesOrder(2, 20))  // DROPPED
    .then(observerProcessesOrder(1, 10))  // OK - extends chain
    // Now round 3 could work if round 2 wasn't dropped
    .then(observerProcessesOrder(3, 30))  // DROPPED - parent is round 2, which was dropped

    .expect(
      observer.orderedChain == Set((0, 0), (1, 10)) and
      observer.droppedBlocks == Set((2, 20), (3, 30))
    )
  }

  // ============================================================================
  // SAFETY CHECKS
  // ============================================================================

  /// Safety holds even with drops
  run safetyWithDropsTest = {
    initWithForks(Set())
    .then(consensusOrdersCommitted(0))
    .then(consensusOrdersCommitted(1))
    .then(consensusCommits(0))

    // Out of order causes drop
    .then(observerProcessesOrder(1, 10))  // DROPPED
    .then(observerProcessesOrder(0, 0))   // OK
    .then(observerProcessesCommit(0, 0))

    .expect(
      safetyInvariant and
      not(noBlocksDropped)
    )
  }
}
