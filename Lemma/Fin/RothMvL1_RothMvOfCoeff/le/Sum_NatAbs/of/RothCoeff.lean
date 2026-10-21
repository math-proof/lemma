import Mathlib
import Lemma.Fin.RothMvL1_Sum.le.Sum_RothMvL1
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvL1_ofCoeff_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ} {r : Fin m → ℕ}
-- given
  (c : RothCoeff r) :
-- imply
  rothMvL1 (rothMvOfCoeff c) ≤ ∑ j, (c j).natAbs := by
-- proof
  classical
  have hmono (i : RothMvIndex m) (a : ℤ) :
    rothMvL1 (MvPolynomial.monomial i a) = a.natAbs := by
    change rothFinsuppL1 (Finsupp.single i a) = a.natAbs
    if ha : a = 0 then
      simp [ha, rothFinsuppL1]
    else
      simp [rothFinsuppL1, ha]
  unfold rothMvOfCoeff
  calc
    _ ≤ ∑ j ∈ Finset.univ,
          rothMvL1 (MvPolynomial.monomial (rothBoxIndex j) (c j)) :=
      RothMvL1_Sum.le.Sum_RothMvL1 Finset.univ _
    _ = ∑ j, (c j).natAbs := by
      simp [hmono]


-- created on 2026-10-21
