import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothRidoutAuxMatrix_complement_row](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (α : ℝ)
  {m : ℕ}
  (r : Fin m → ℕ)
  (γ : ℝ)
-- given
  (i : RothLowIndex r γ)
  (j : RothBox r) :
-- imply
  rothRidoutAuxMatrix α r γ
    (i, Fin.last ((rothIntegralPolynomial α).natDegree + 1)) j =
    if j = rothRidoutBoxComplement r i.1 then 1 else 0 := by
-- proof
  simp [rothRidoutAuxMatrix]


-- created on 2026-10-21
