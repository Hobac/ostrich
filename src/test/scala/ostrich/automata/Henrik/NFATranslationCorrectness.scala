package ostrich.automata.Henrik

import org.scalacheck.Properties
import ostrich.automata.afa2.concrete.{AFA2StateDuplicator, AFA2StateExpander, AFA2TestHelper, NFATranslator, NFATranslatorParallel}

object NFATranslationCorrectness extends Properties("AFA2") {

  property("Parallel-NFATranslator tested against Lazy-NFATranslator") = {
    val automataCount = 10L
    var seed = 0L

    var parallelTime = 0L
    var lazyTime = 0L
    var allEquivalent = true

    while (seed < automataCount && allEquivalent) {
      val aut = AFA2TestHelper.randomAFA2(seed, 10000, 5, 0.5)
      val safa = AFA2StateDuplicator(aut)
      println(safa.states.size + " states in the automaton")

      val parallelStart = System.nanoTime()
      val parallel = NFATranslatorParallel(AFA2StateDuplicator(safa))
      parallelTime += System.nanoTime() - parallelStart

      val lazyStart = System.nanoTime()
      val lazyTown = NFATranslator(AFA2StateDuplicator(safa), null)
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

    val fasterPercent =
      (lazyTime.toDouble - parallelTime.toDouble) / lazyTime.toDouble * 100.0

    val speedup =
      lazyTime.toDouble / parallelTime.toDouble

    println()
    println(f"Parallel: $parallelSeconds%.3f s")
    println(f"Lazy:     $lazySeconds%.3f s")
    println(f"Parallel is $fasterPercent%.2f%% faster")
    println(f"Speedup:  ${speedup}%.2fx")

    allEquivalent
  }
}