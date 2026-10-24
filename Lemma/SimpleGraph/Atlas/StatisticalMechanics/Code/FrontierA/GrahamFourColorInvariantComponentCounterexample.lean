import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamFourColorInvariantComponentCounterexample
open Finset Classical StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[exists_invariantComponentSelector_parallel_counterexample](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantComponentCounterexample.lean)
-/
@[path]
private lemma exists_invariantComponentSelector_parallel_counterexample_eq :
-- imply
  ∃ (ends : Fin 6 -> Sym2 (Fin 4)) (c : ↑(Finset.univ : Finset (Fin 6)) -> Fin 4), LeftPattern ends Finset.univ {0, 1} {1, 2} 1 3 c ∧ ¬ RowsDisconnect ends Finset.univ (balancedSwap Finset.univ (invariantMiddleTransfer ends Finset.univ c 1) (invariantOuterTransfer ends Finset.univ c 0 3) c) 1 3 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_invariantComponentSelector_parallel_counterexample


-- created on 2026-10-23
