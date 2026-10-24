import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamFourColorStrictDescentCounterexample
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[exists_canonicalTransferStrictDescent_counterexample](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorStrictDescentCounterexample.lean)
-/
@[path]
private lemma exists_canonicalTransferStrictDescent_counterexample_eq :
-- imply
  ∃ (ends : Fin 7 -> Sym2 (Fin 6)) (c d : ↑(Finset.univ : Finset (Fin 7)) -> Fin 4), LeftPattern ends Finset.univ {4, 0} {0, 5} 0 1 c ∧ LeftPattern ends Finset.univ {4, 0} {0, 5} 0 1 d ∧ fourColorMaskProfile Finset.univ c = fourColorMaskProfile Finset.univ d ∧ ¬ RowsDisconnect ends Finset.univ (balancedSwap Finset.univ (canonicalMiddleTransfer ends Finset.univ c 0 1) (canonicalOuterTransfer ends Finset.univ c 0 1) d) 0 1 ∧ canonicalTransferUnion ends Finset.univ 0 1 c ⊂ canonicalTransferUnion ends Finset.univ 0 1 d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalTransferStrictDescent_counterexample


-- created on 2026-10-23
