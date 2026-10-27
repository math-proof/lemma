import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma IsLocalRing.mul_self_eq_one_iff_of_isUnit_two
  {R : Type} [CommRing R] [IsLocalRing R]
  (u : R)
  -- given
  (htwo : IsUnit (2 : R)) :
  -- imply
  u * u = 1 ↔ u = 1 ∨ u = -1 := by
  -- proof
  constructor
  ·
    intro hu
    have hfac : (u - 1) * (u + 1) = 0 := by
      have : (u - 1) * (u + 1) = u * u - 1 := by
        ring
      rw [this, hu, sub_self]
    have h2' : IsUnit ((u + 1) + (1 - u)) := by
      have : (u + 1) + (1 - u) = (2 : R) := by
        ring
      rwa [this]
    obtain h | h := IsLocalRing.isUnit_or_isUnit_of_isUnit_add h2'
    · refine Or.inl (sub_eq_zero.mp ((h.mul_left_eq_zero).mp hfac))
    ·
      have hfac' : (u + 1) * (1 - u) = 0 := by
        have : (u + 1) * (1 - u) = -((u - 1) * (u + 1)) := by
          ring
        rw [this, hfac, neg_zero]
      refine Or.inr (eq_neg_of_add_eq_zero_left ((h.mul_left_eq_zero).mp hfac'))
  ·
    intro hdisj
    obtain rfl | rfl := hdisj
    · ring
    · ring

/--
[IsLocalRing_sq_eq_one_iff_of_isUnit_two](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_sq_eq_one_iff_of_isUnit_two.lean)
-/
@[path]
private lemma main
  {R : Type} [CommRing R] [IsLocalRing R]
  (u : R)
  -- given
  (htwo : IsUnit (2 : R)) :
  -- imply
  u ^ 2 = 1 ↔ u = 1 ∨ u = -1 := by
  -- proof
  rw [sq]
  refine IsLocalRing.mul_self_eq_one_iff_of_isUnit_two u htwo


-- created on 2026-10-20
