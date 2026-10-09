import Mathlib
import sympy.Basic

open CategoryTheory groupCohomology

/--
[groupCohomology_cocycles1_conj_apply_sub_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_cocycles1_conj_apply_sub_eq.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G]
  {A : Rep.{u} k G}
  {c : cocycles₁ A}
  {g s : G} :
-- imply
  A.ρ g (c (g⁻¹ * s * g)) - c s = A.ρ s (c g) - c g := by
-- proof
  have hco := (mem_cocycles₁_iff (⇑c)).1 c.2
  have h1 : c (g⁻¹ * s * g) = A.ρ g⁻¹ (c (s * g)) + c g⁻¹ := by
    rw [mul_assoc]; exact hco g⁻¹ (s * g)
  have h2 : c (s * g) = A.ρ s (c g) + c s := hco s g
  rw [h1, map_add, h2, ← Module.End.mul_apply (A.ρ g) (A.ρ g⁻¹), ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply, cocycles₁_map_inv c g]
  abel


-- created on 2026-10-05
