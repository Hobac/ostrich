package ostrich.automata.Optimization

import org.scalacheck.Properties
import ostrich.automata.afa2.concrete.{AFA2TestHelper}

object Performance extends Properties("AFA2") {

  property("compare minimizeStates() and optimizeUntilFixpoint() on 250 random automata") = {
    val automataCount = 250L
    var seed = 0L

    var totalOriginalStates = 0
    var totalMinimizedStates = 0
    var totalOptimizeUntilFixpointStates = 0
    var optimizeUntilFixpointBetter = 0
    var minimizeStatesBetter = 0
    var bothSame = 0

    while (seed < automataCount) {
      val automaton = AFA2TestHelper.randomAFA2(seed)

      val minimizedAutomaton = automaton.minimizeStates()
      val partitionRefinedAutomaton = automaton.optimizeUntilFixpoint()

      val originalStateCount = automaton.states.size
      val minimizedStateCount = minimizedAutomaton.states.size
      val partitionRefinedStateCount = partitionRefinedAutomaton.states.size

      totalOriginalStates = totalOriginalStates + originalStateCount
      totalMinimizedStates = totalMinimizedStates + minimizedStateCount
      totalOptimizeUntilFixpointStates = totalOptimizeUntilFixpointStates + partitionRefinedStateCount

      if (partitionRefinedStateCount < minimizedStateCount) {
        optimizeUntilFixpointBetter = optimizeUntilFixpointBetter + 1
      } else if (minimizedStateCount < partitionRefinedStateCount) {
        minimizeStatesBetter = minimizeStatesBetter + 1
      } else {
        bothSame = bothSame + 1
      }

      seed = seed + 1L
    }

    val minimizeStatesReduction =
      100.0 - (totalMinimizedStates.toDouble * 100.0 / totalOriginalStates.toDouble)

    val optimizeUntilFixpointReduction =
      100.0 - (totalOptimizeUntilFixpointStates.toDouble * 100.0 / totalOriginalStates.toDouble)

    println("Compared " + automataCount + " random automata")
    println("Original total states: " + totalOriginalStates)
    println("minimizeStates total states: " + totalMinimizedStates)
    println("optimizeUntilFixpoint total states: " + totalOptimizeUntilFixpointStates)

    println("minimizeStates reduction: " + minimizeStatesReduction + "%")
    println("optimizeUntilFixpoint reduction: " + optimizeUntilFixpointReduction + "%")

    println("optimizeUntilFixpoint produced smaller automata in " + optimizeUntilFixpointBetter + " cases")
    println("minimizeStates produced smaller automata in " + minimizeStatesBetter + " cases")
    println("Both produced same-size automata in " + bothSame + " cases")

    optimizeUntilFixpointReduction >= 0.0
  }
}