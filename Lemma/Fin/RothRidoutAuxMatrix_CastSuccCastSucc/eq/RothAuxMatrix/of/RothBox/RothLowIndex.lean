import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothRidoutAuxMatrix_old_row](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (α : ℝ)
  {m : ℕ}
  (r : Fin m → ℕ)
  (γ : ℝ)
-- given
  (i : RothLowIndex r γ)
  (k : Fin (rothIntegralPolynomial α).natDegree)
  (j : RothBox r) :
-- imply
  rothRidoutAuxMatrix α r γ (i, k.castSucc.castSucc) j =
    rothAuxMatrix α r γ (i, k) j := by
-- proof
  simp [rothRidoutAuxMatrix]


-- created on 2026-10-21
