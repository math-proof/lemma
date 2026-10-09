import Mathlib
import sympy.Basic


/--
[eq_one_of_isNilpotent_sub_one_of_pow_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_eq_one_of_isNilpotent_sub_one_of_pow_eq_one.lean)
-/
@[path]
private lemma main
  [Ring A]
  {u : A}
  {m : ℕ}
-- given
  (hu : IsNilpotent (u - 1))
  (hm : IsUnit (m : A))
  (h : u ^ m = 1) :
-- imply
  u = 1 := by
-- proof
  have hs : (∑ i ∈ Finset.range m, u ^ i) * (u - 1) = 0 := by
    rw [geom_sum_mul, h, sub_self]

  have hdecomp : (∑ i ∈ Finset.range m, u ^ i) =
      (m : A) + ∑ i ∈ Finset.range m, (u ^ i - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    abel
  have hnil_i : ∀ i : ℕ, IsNilpotent (u ^ i - 1) := fun i => by
    have hgeom : u ^ i - 1 = (∑ j ∈ Finset.range i, u ^ j) * (u - 1) := (geom_sum_mul u i).symm
    rw [hgeom]
    refine Commute.isNilpotent_mul_left ?_ hu
    exact Commute.sum_left _ _ _ fun j _ =>
      ((Commute.refl u).pow_left j).sub_right (Commute.one_right _)
  have hnil_sum : IsNilpotent (∑ i ∈ Finset.range m, (u ^ i - 1)) :=
    Commute.isNilpotent_sum (fun i _ => hnil_i i) fun i j _ _ =>
      (((Commute.refl u).pow_pow i j).sub_left (Commute.one_left _)).sub_right
        (Commute.one_right _)
  have hunit : IsUnit (∑ i ∈ Finset.range m, u ^ i) := by
    rw [hdecomp]
    exact hnil_sum.isUnit_add_left_of_commute hm (Commute.sum_left _ _ _ fun i _ =>
      (Nat.cast_commute m _).symm)
  have hz : u - 1 = 0 := (hunit.mul_right_eq_zero).1 hs
  exact sub_eq_zero.1 hz


-- created on 2026-10-05
