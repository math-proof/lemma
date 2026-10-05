import Mathlib
import sympy.Basic

open CategoryTheory Module groupCohomology

/--
[groupCohomology_cocycles1_apply_eq_zero_of_mem_closure](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_cocycles1_apply_eq_zero_of_mem_closure.lean)
-/
@[main]
private lemma main
  {k G : Type u} [CommRing k] [Group G]
  {M : Rep k G}
  {c : cocycles₁ M}
  {s : Set G}
  {g : G}
-- given
  (hs : ∀ g ∈ s, c g = 0)
  (hg : g ∈ Subgroup.closure s) :
-- imply
  c g = 0 := by
-- proof
  have hcoc := (mem_cocycles₁_iff (A := M) ⇑c).1 c.2
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hs x hx
  | one => exact cocycles₁_map_one c
  | mul x y _ _ hx hy => rw [hcoc x y, hy, map_zero, zero_add, hx]
  | inv x _ hx =>
      have h := hcoc x⁻¹ x
      rw [inv_mul_cancel, cocycles₁_map_one, hx, map_zero, zero_add] at h
      exact h.symm


-- created on 2026-10-05
