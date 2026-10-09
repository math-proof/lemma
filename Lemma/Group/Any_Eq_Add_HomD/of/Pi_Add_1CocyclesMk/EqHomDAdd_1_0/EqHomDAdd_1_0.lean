import Mathlib
import sympy.Basic

open CategoryTheory groupCohomology

/--
[groupCohomology_exists_eq_add_d_of_pi_cocyclesMk_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_exists_eq_add_d_of_pi_cocyclesMk_eq.lean)
-/
@[path]
private lemma main
  {k G : Type} [CommRing k] [Group G]
  {A : Rep.{0} k G}
  {n : ℕ}
  {x x' : (Fin (n + 1) → G) → A}
-- given
  (hx : (inhomogeneousCochains.d A (n + 1)).hom x = 0)
  (hx' : (inhomogeneousCochains.d A (n + 1)).hom x' = 0)
  (h : groupCohomology.π A (n + 1) (groupCohomology.cocyclesMk x hx) = groupCohomology.π A (n + 1) (groupCohomology.cocyclesMk x' hx')) :
-- imply
  ∃ y : (Fin n → G) → A, x = x' + (inhomogeneousCochains.d A n).hom y := by
-- proof
  set K := inhomogeneousCochains A with hK
  have hex : (ShortComplex.mk (K.toCycles n (n + 1)) (K.homologyπ (n + 1)) (K.toCycles_comp_homologyπ n (n + 1))).Exact :=
    ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel n (n + 1) (by simp))
  rw [ShortComplex.moduleCat_exact_iff] at hex
  obtain ⟨y, hy⟩ := hex (groupCohomology.cocyclesMk x hx - groupCohomology.cocyclesMk x' hx') (by
    show (K.homologyπ (n + 1)) (groupCohomology.cocyclesMk x hx - groupCohomology.cocyclesMk x' hx') = 0
    rw [map_sub, sub_eq_zero]
    exact h)
  refine ⟨y, ?_⟩
  have h2 := congrArg (iCocycles A (n + 1)) hy
  change (K.toCycles n (n + 1) ≫ K.iCycles (n + 1)) y = _ at h2
  rw [HomologicalComplex.toCycles_i, map_sub, iCocycles_mk, iCocycles_mk, inhomogeneousCochains.d_def] at h2
  rw [h2, add_sub_cancel]


-- created on 2026-10-05
