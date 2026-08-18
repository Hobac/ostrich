package ostrich.automata.Henrik

import org.scalacheck.Properties
import ostrich.automata.afa2.concrete.{AFA2StateDuplicator, AFA2TestHelper, NFATranslator, NFATranslatorParallel}

object NFATranslationPerformance extends Properties("AFA2") {

  property("Parallel-NFATranslator performance") = {
    val automataCount = 100L
    var seed = 0L
    var time = 0L

    while (seed < automataCount) {
      val aut = AFA2TestHelper.randomAFA2(seed, 1000, 10, 0.5)
      val safa = AFA2StateDuplicator(aut)
      println(safa.states.size + " states in 2AFA")

      val start = System.nanoTime()
      val nfa = NFATranslatorParallel(safa)
      println(nfa.states.size + " states in NFA")
      time += (System.nanoTime() - start)

      println((seed.toFloat / automataCount.toFloat) * 100 + "% done...")

      seed = seed + 1L
    }

    val seconds = time.toDouble / 1e9
    println(f"Time: $seconds%.3f s")

    true
  }
}