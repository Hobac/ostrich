package ostrich.automata.Henrik

import org.scalacheck.Properties
import ostrich.automata.afa2.concrete.{AFA2StateDuplicator, AFA2StateExpander, AFA2TestHelper, NFATranslator, NFATranslatorParallel}

object NFATranslationCorrectness extends Properties("AFA2") {

  property("Parallel-NFATranslator tested against Lazy-NFATranslator") = {
    val automataCount = 100L
    var seed = 0L

    var parallelTime = 0L
    var lazyTime = 0L
    var allEquivalent = true

    while (seed < automataCount && allEquivalent) {
      val aut = AFA2TestHelper.randomAFA2(seed, 1000, 10, 0.5)
      val safa = AFA2StateDuplicator(aut)
      println(safa.states.size + " states in the automaton")

      val parallelStart = System.nanoTime()
      val parallel = NFATranslatorParallel(safa)
      parallelTime += System.nanoTime() - parallelStart

      val lazyStart = System.nanoTime()
      val lazyTown = NFATranslator(safa, null)
      lazyTime += System.nanoTime() - lazyStart

      val parallelMinusLazyTown = parallel & !lazyTown
      val lazyTownMinusParallel = lazyTown & !parallel

      val equivalent = parallelMinusLazyTown.isEmpty && lazyTownMinusParallel.isEmpty

      println((seed.toFloat / automataCount.toFloat) * 100 + "% done...")

      if (!equivalent) {
        println("Counterexample seed: " + seed)
        println(aut)
        allEquivalent = false
      }

      seed = seed + 1L
    }

    val parallelSeconds = parallelTime / 1e9
    val lazySeconds = lazyTime / 1e9

    val speedup =
      lazyTime.toDouble / parallelTime.toDouble

    println()
    println(f"Parallel: $parallelSeconds%.3f s")
    println(f"Lazy:     $lazySeconds%.3f s")
    println(f"Speedup:  ${speedup}%.2fx")

    allEquivalent
  }
}