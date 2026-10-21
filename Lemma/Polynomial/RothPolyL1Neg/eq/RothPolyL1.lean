import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPolyL1_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (P : ℤ[X]) :
-- imply
  rothPolyL1 (-P) = rothPolyL1 P := by
-- proof
  classical
  unfold rothPolyL1 rothFinsuppL1
  rw [toFinsupp_neg]
  change ∑ a ∈ (-P.toFinsupp.coeff).support, ((-P.toFinsupp.coeff) a).natAbs =
    ∑ a ∈ P.toFinsupp.coeff.support, (P.toFinsupp.coeff a).natAbs
  rw [Finsupp.support_neg]
  congr with a
  apply Int.natAbs_neg


-- created on 2026-10-21
