import Mathlib
import Lemma.Fin.RothMvL1_Sum.le.Sum_RothMvL1
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvL1_hasse_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
-- given
  (P : MvPolynomial (Fin m) ℤ)
  (i : RothMvIndex m)
  (r : Fin m → ℕ)
  (hdeg : rothDegreeBound P r) :
-- imply
  rothMvL1 (rothMvHasse i P) ≤ 2 ^ (∑ h, r h) * rothMvL1 P := by
-- proof
  classical
  have hmono (j : RothMvIndex m) (c : ℤ) :
    rothMvL1 (MvPolynomial.monomial j c) = c.natAbs := by
    change rothFinsuppL1 (Finsupp.single j c) = c.natAbs
    if hc : c = 0 then
      simp [hc, rothFinsuppL1]
    else
      simp [rothFinsuppL1, hc]
  have hbound (j : RothMvIndex m) (hj : j ∈ P.support) :
    ∏ h, Nat.choose (j h) (i h) ≤ 2 ^ (∑ h, r h) := calc
    _ ≤ ∏ h, 2 ^ j h := by
      gcongr with h
      exact Nat.choose_le_two_pow (j h) (i h)
    _ ≤ ∏ h, 2 ^ r h := by
      gcongr with h
      exact hdeg j hj h
    _ = 2 ^ (∑ h, r h) := Finset.prod_pow_eq_pow_sum Finset.univ r 2
  unfold rothMvHasse
  rw [Finsupp.sum]
  calc
    _ ≤ ∑ j ∈ P.support,
        rothMvL1 (MvPolynomial.monomial (j - i) ((∏ h, (Nat.choose (j h) (i h) : ℤ)) * P.coeff j)) :=
      RothMvL1_Sum.le.Sum_RothMvL1 P.support _
    _ = ∑ j ∈ P.support, (∏ h, Nat.choose (j h) (i h)) * (P.coeff j).natAbs := by
      congr with j
      rw [hmono, Int.natAbs_mul, ← Nat.cast_prod, Int.natAbs_natCast]
    _ ≤ ∑ j ∈ P.support, 2 ^ (∑ h, r h) * (P.coeff j).natAbs := by
      gcongr with j hj
      exact hbound j hj
    _ = 2 ^ (∑ h, r h) * rothMvL1 P := by
      unfold rothMvL1 rothFinsuppL1
      rw [← MvPolynomial.finsupp_support_eq_support, Finset.mul_sum]


-- created on 2026-10-21
