import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvL1_coeff_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (P : MvPolynomial (Fin m) ℤ) (i : RothMvIndex m) :
-- imply
  (P.coeff i).natAbs ≤ rothMvL1 P := by
-- proof
  classical
  unfold rothMvL1 rothFinsuppL1
  if ha : P.coeff i = 0 then
    simp [ha]
  else
    exact Finset.single_le_sum (fun b _ ↦ Nat.zero_le (P.coeff b).natAbs)
      (Finsupp.mem_support_iff.mpr ha)


-- created on 2026-10-21
