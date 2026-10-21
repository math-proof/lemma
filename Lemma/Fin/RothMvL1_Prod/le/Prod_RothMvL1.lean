import Mathlib
import Lemma.Fin.RothMvL1Mul.le.MulRothSMvL1
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvL1_finset_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (s : Finset J) (P : J → MvPolynomial (Fin m) ℤ) :
-- imply
  rothMvL1 (∏ j ∈ s, P j) ≤ ∏ j ∈ s, rothMvL1 (P j) := by
-- proof
  classical
  have hone : rothMvL1 (1 : MvPolynomial (Fin m) ℤ) = 1 := by
    have hmono (i : RothMvIndex m) (c : ℤ) :
      rothMvL1 (MvPolynomial.monomial i c) = c.natAbs := by
      change rothFinsuppL1 (Finsupp.single i c) = c.natAbs
      if hc : c = 0 then
        simp [hc, rothFinsuppL1]
      else
        simp [rothFinsuppL1, hc]
    rw [show (1 : MvPolynomial (Fin m) ℤ) = MvPolynomial.monomial 0 1 by simp]
    rw [hmono]
    norm_num
  induction s using Finset.induction_on with
  | empty =>
    simp [hone]
  | @insert j s hjs ih =>
    simp only [Finset.prod_insert hjs]
    exact (RothMvL1Mul.le.MulRothSMvL1 _ _).trans (Nat.mul_le_mul_left _ ih)


-- created on 2026-10-21
