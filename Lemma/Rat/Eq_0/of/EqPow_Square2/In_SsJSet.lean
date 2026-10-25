import Mathlib
import sympy.Basic
import Lemma.ModularCurve.SupersingularModuli
import Lemma.Int.P2MUtil

open ModularCurve WeierstrassCurve

/--
[ModularCurve_eq_zero_of_mem_ssJSet_two](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_eq_zero_of_mem_ssJSet_two.lean)
-/

private lemma  two_eq_zero (k : Type*) [Ring k] [CharP k 2] : (2 : k) = 0 := by
  simpa using CharP.cast_eq_zero k 2

private lemma  cast1728_eq_zero_of_two (k : Type*) [Ring k] [CharP k 2] : (1728 : k) = 0 := by
  rw [show (1728 : k) = 2 * 864 by norm_num, two_eq_zero k, zero_mul]

private lemma  exists_two_torsion_char_two {k : Type*} [Field k] [CharP k 2] [DecidableEq k]
  (a : k) (h0 : a ≠ 0) (ha4 : a ^ 4 = a) :
  ∃ P : (ofJNe0Or1728 a).toAffine.Point, P ≠ 0 ∧ 2 • P = 0 := by
  have h1728 : (1728 : k) = 0 := cast1728_eq_zero_of_two k
  have ha3 : a ^ 3 = 1 := by
    have : a * (a ^ 3 - 1) = 0 := by rw [mul_sub, mul_one, ← pow_succ', ha4, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h0
    · exact sub_eq_zero.mp h
  have hneg : ∀ x : k, -x = x := fun x => CharTwo.neg_eq x
  have heq : (ofJNe0Or1728 a).toAffine.Equation 0 a := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [ofJNe0Or1728, h1728, sub_zero]
    have : a ^ 5 = a ^ 2 := by rw [show (5 : ℕ) = 3 + 2 by norm_num, pow_add, ha3, one_mul]
    rw [this]
    linear_combination a ^ 2 * two_eq_zero k
  haveI : Fact (IsUnit a) := ⟨isUnit_iff_ne_zero.mpr h0⟩
  haveI : Fact (IsUnit (a - 1728)) := ⟨by rw [h1728, sub_zero]; exact isUnit_iff_ne_zero.mpr h0⟩
  have hns : (ofJNe0Or1728 a).toAffine.Nonsingular 0 a :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular (W := ofJNe0Or1728 a)).mp heq
  refine ⟨WeierstrassCurve.Affine.Point.some _ _ hns, WeierstrassCurve.Affine.Point.some_ne_zero hns, ?_⟩
  have hy : a = (ofJNe0Or1728 a).toAffine.negY 0 a := by
    simp only [WeierstrassCurve.Affine.negY, ofJNe0Or1728, mul_zero, sub_zero]
    exact (hneg a).symm
  rw [two_nsmul]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy
@[path]
private lemma main
  [Field k] [CharP k 2] [DecidableEq k]
  {a : k}
-- given
  (ha : a ∈ ssJSet 2 k)
  (ha2 : a ^ (2 ^ 2) = a) :
-- imply
  a = 0 := by
-- proof
  by_contra h0
  haveI : Fact (IsUnit a) := ⟨isUnit_iff_ne_zero.mpr h0⟩
  haveI : Fact (IsUnit (a - 1728)) :=
    ⟨by rw [cast1728_eq_zero_of_two k, sub_zero]; exact isUnit_iff_ne_zero.mpr h0⟩
  obtain ⟨P, hP0, hP2⟩ := exists_two_torsion_char_two a h0 (by simpa using ha2)
  exact hP0 (ha (ofJNe0Or1728 a) (ofJNe0Or1728_j a) P hP2)


-- created on 2026-10-23
