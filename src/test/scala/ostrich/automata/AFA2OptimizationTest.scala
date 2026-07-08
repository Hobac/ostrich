package ostrich.automata.afa2.concrete

import ostrich.automata.afa2.{Right, Left, StepTransition}
import org.scalacheck.Properties

object AFA2OptimizationTest extends Properties("AFA2") {
  // get a random 2AFA
  // we only use right-transitions
  // this avoids looping
  // initial states only have outgoing transitions
  // final states only incoming ones
  // so that StateDuplicator does not have any issues
  private def randomAFA2(
                          seed: Long,
                          stateCount: Int = 8,
                          alphabet: IndexedSeq[Int] = Vector('a'.toInt, 'b'.toInt),
                          maxTargetCount: Int = 2,
                          universalProbability: Double = 0.2
                        ): AFA2 = {

    val random = new scala.util.Random(seed)

    val initialState = 0
    val finalState = stateCount - 1

    val initialStates = Seq(initialState)
    val finalStates = Seq(finalState)

    var transitions = Map[Int, Seq[StepTransition]]()

    for (state <- 0 until finalState) {
      var outgoingTransitions = Seq[StepTransition]()

      for (label <- alphabet) {
        val targets =
          randomForwardTargets(
            random = random,
            currentState = state,
            finalState = finalState,
            maxTargetCount = maxTargetCount,
            universalProbability = universalProbability
          )

        val transition = StepTransition(label, Right, targets)
        outgoingTransitions = outgoingTransitions :+ transition
      }

      transitions = transitions + (state -> outgoingTransitions)
    }

    AFA2(initialStates, finalStates, transitions)
  }

  private def randomForwardTargets(
                                    random: scala.util.Random,
                                    currentState: Int,
                                    finalState: Int,
                                    maxTargetCount: Int,
                                    universalProbability: Double
                                  ): Seq[Int] = {

    val firstPossibleTarget = currentState + 1
    val possibleTargets = firstPossibleTarget to finalState
    var targetCount = 1

    if (random.nextDouble() < universalProbability) {
      targetCount = 2 + random.nextInt(maxTargetCount - 1)
    }

    if (targetCount > possibleTargets.size) {
      targetCount = possibleTargets.size
    }

    var targets = Seq[Int]()

    while (targets.size < targetCount) {
      val randomIndex = random.nextInt(possibleTargets.size)
      val target = possibleTargets(randomIndex)

      if (!targets.contains(target)) {
        targets = targets :+ target
      }
    }

    targets
  }

  property("partitionRefinement preserves language (hand crafted test)") = {
    val aut = AFA2(
      initialStates = Seq(0),
      finalStates = Seq(9),
      transitions = Map(
        0 -> Seq(
          StepTransition('a'.toInt, Right, Seq(1)),
          StepTransition('b'.toInt, Right, Seq(2))
        ),

        // 1 and 3 are intentionally equivalent
        1 -> Seq(
          StepTransition('a'.toInt, Right, Seq(3)),
          StepTransition('b'.toInt, Right, Seq(4))
        ),
        3 -> Seq(
          StepTransition('a'.toInt, Right, Seq(3)),
          StepTransition('b'.toInt, Right, Seq(4))
        ),

        // 2 and 5 are intentionally equivalent
        2 -> Seq(
          StepTransition('a'.toInt, Right, Seq(5)),
          StepTransition('b'.toInt, Right, Seq(6))
        ),
        5 -> Seq(
          StepTransition('a'.toInt, Right, Seq(5)),
          StepTransition('b'.toInt, Right, Seq(6))
        ),

        // 4 and 7 are intentionally equivalent
        4 -> Seq(
          StepTransition('a'.toInt, Right, Seq(7)),
          StepTransition('b'.toInt, Right, Seq(9))
        ),
        7 -> Seq(
          StepTransition('a'.toInt, Right, Seq(7)),
          StepTransition('b'.toInt, Right, Seq(9))
        ),

        // 6 and 8 are intentionally equivalent
        6 -> Seq(
          StepTransition('a'.toInt, Right, Seq(8)),
          StepTransition('b'.toInt, Right, Seq(9))
        ),
        8 -> Seq(
          StepTransition('a'.toInt, Right, Seq(8)),
          StepTransition('b'.toInt, Right, Seq(9))
        )
      )
    )

    val reduced = aut.partitionRefinement()

    val beforeNFA =
      NFATranslator(AFA2StateDuplicator(aut), null)

    val afterNFA =
      NFATranslator(AFA2StateDuplicator(reduced), null)

    val beforeMinusAfter = beforeNFA & !afterNFA
    val afterMinusBefore = afterNFA & !beforeNFA

    reduced.states.size < aut.states.size &&
      beforeMinusAfter.isEmpty &&
      afterMinusBefore.isEmpty
  }

  // TODO: Make sure that partition refinement does not produce an automaton that can not be categorized
  // TODO: If that can not be ensured, then adjust StateDuplicator for the edge cases
  property("partitionRefinement preserves language (1000 random automata)") = {
    var allEquivalent = true
    var seed = 0L

    while (seed < 1000L && allEquivalent) {
      val aut = randomAFA2(seed)
      val reduced = aut.partitionRefinement()

      val beforeNFA = NFATranslator(AFA2StateDuplicator(aut), null)
      val afterNFA = NFATranslator(AFA2StateDuplicator(reduced), null)

      val beforeMinusAfter = beforeNFA & !afterNFA
      val afterMinusBefore = afterNFA & !beforeNFA

      val equivalent =
        beforeMinusAfter.isEmpty && afterMinusBefore.isEmpty

      if (!equivalent) {
        println("Counterexample seed: " + seed)
        println("Original AFA2:")
        println(aut)
        println("Reduced AFA2:")
        println(reduced)
        allEquivalent = false
      }

      seed = seed + 1L
    }

    allEquivalent
  }

  property("compare minimizeStates and partitionRefinement on 1000 random automata") = {
    val automataCount = 1000L

    var seed = 0L

    var totalOriginalStates = 0
    var totalMinimizedStates = 0
    var totalPartitionRefinedStates = 0
    var partitionRefinementBetter = 0
    var minimizeStatesBetter = 0
    var bothSame = 0

    while (seed < automataCount) {
      val automaton = randomAFA2(seed)

      val minimizedAutomaton = automaton.minimizeStates()
      val partitionRefinedAutomaton = automaton.partitionRefinement()

      val originalStateCount = automaton.states.size
      val minimizedStateCount = minimizedAutomaton.states.size
      val partitionRefinedStateCount = partitionRefinedAutomaton.states.size

      totalOriginalStates = totalOriginalStates + originalStateCount
      totalMinimizedStates = totalMinimizedStates + minimizedStateCount
      totalPartitionRefinedStates = totalPartitionRefinedStates + partitionRefinedStateCount

      if (partitionRefinedStateCount < minimizedStateCount) {
        partitionRefinementBetter = partitionRefinementBetter + 1
      } else if (minimizedStateCount < partitionRefinedStateCount) {
        minimizeStatesBetter = minimizeStatesBetter + 1
      } else {
        bothSame = bothSame + 1
      }

      seed = seed + 1L
    }

    val minimizeStatesReduction =
      100.0 - (totalMinimizedStates.toDouble * 100.0 / totalOriginalStates.toDouble)

    val partitionRefinementReduction =
      100.0 - (totalPartitionRefinedStates.toDouble * 100.0 / totalOriginalStates.toDouble)

    println("Compared " + automataCount + " random automata")
    println("Original total states: " + totalOriginalStates)
    println("minimizeStates total states: " + totalMinimizedStates)
    println("partitionRefinement total states: " + totalPartitionRefinedStates)

    println("minimizeStates reduction: " + minimizeStatesReduction + "%")
    println("partitionRefinement reduction: " + partitionRefinementReduction + "%")

    println("partitionRefinement produced smaller automata in " + partitionRefinementBetter + " cases")
    println("minimizeStates produced smaller automata in " + minimizeStatesBetter + " cases")
    println("Both produced same-size automata in " + bothSame + " cases")

    partitionRefinementReduction >= 0.0
  }
}