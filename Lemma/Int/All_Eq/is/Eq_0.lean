import Mathlib
import sympy.Basic

open CategoryTheory Module groupCohomology

/--
[groupCohomology_cocycles1_forall_apply_mul_right_eq_iff_apply_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_cocycles1_forall_apply_mul_right_eq_iff_apply_eq_zero.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G]
  {M : Rep k G}
  {c : cocycles₁ M}
  {u : G} :
-- imply
  (∀ g : G, c (g * u) = c g) ↔ c u = 0 := by
-- proof
  have hcoc := (mem_cocycles₁_iff (A := M) ⇑c).1 c.2
  constructor
  · intro h
    have h1 := h 1
    rw [one_mul, cocycles₁_map_one] at h1
    exact h1
  · intro hu g
    rw [hcoc g u, hu, map_zero, zero_add]


-- created on 2026-10-05
