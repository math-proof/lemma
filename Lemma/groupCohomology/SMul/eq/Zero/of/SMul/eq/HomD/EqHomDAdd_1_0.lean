import Mathlib
import sympy.Basic

open CategoryTheory groupCohomology

/--
[groupCohomology_zsmul_pi_cocyclesMk_eq_zero_of_eq_d](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_zsmul_pi_cocyclesMk_eq_zero_of_eq_d.lean)
-/
@[main]
private lemma main
  [Group G]
  {A : Rep.{0} ℤ G}
  {n : ℕ}
  {m : ℤ}
  {x : (Fin (n + 1) → G) → A}
  {y : (Fin n → G) → A}
-- given
  (hx : (inhomogeneousCochains.d A (n + 1)).hom x = 0)
  (h : m • x = (inhomogeneousCochains.d A n).hom y) :
-- imply
  m • groupCohomology.π A (n + 1) (groupCohomology.cocyclesMk x hx) = 0 := by
-- proof
  have hsm : m • groupCohomology.cocyclesMk x hx = groupCohomology.toCocycles A n (n + 1) y := by
    apply (ModuleCat.mono_iff_injective (groupCohomology.iCocycles A (n + 1))).mp inferInstance
    show (groupCohomology.iCocycles A (n + 1)).hom (m • groupCohomology.cocyclesMk x hx) =
      (groupCohomology.iCocycles A (n + 1)).hom (groupCohomology.toCocycles A n (n + 1) y)
    rw [map_zsmul]
    have h1 : (groupCohomology.iCocycles A (n + 1)).hom (groupCohomology.cocyclesMk x hx) = x := groupCohomology.iCocycles_mk x hx
    have h2 : (groupCohomology.iCocycles A (n + 1)).hom (groupCohomology.toCocycles A n (n + 1) y) = (inhomogeneousCochains.d A n).hom y := by
      have hti := (inhomogeneousCochains A).toCycles_i n (n + 1)
      rw [inhomogeneousCochains.d_def] at hti
      have := congrArg (fun T => (ModuleCat.Hom.hom T) y) hti
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
      exact this
    rw [h1, h2, h]
  have hπ : (groupCohomology.π A (n + 1)).hom (groupCohomology.toCocycles A n (n + 1) y) = 0 := by
    have := congrArg (fun T => (ModuleCat.Hom.hom T) y) ((inhomogeneousCochains A).toCycles_comp_homologyπ n (n + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] at this
    exact this
  show m • (groupCohomology.π A (n + 1)).hom (groupCohomology.cocyclesMk x hx) = 0
  rw [← map_zsmul, hsm, hπ]


-- created on 2026-10-05
