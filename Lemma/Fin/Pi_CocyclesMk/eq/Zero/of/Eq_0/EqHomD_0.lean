import Mathlib
import sympy.Basic

open CategoryTheory groupCohomology

/--
[groupCohomology_pi_cocyclesMk_eq_zero_of_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_pi_cocyclesMk_eq_zero_of_eq_zero.lean)
-/
@[path]
private lemma main
  {k G : Type} [CommRing k] [Group G]
  {A : Rep.{0} k G}
  {n : ℕ}
  {x : (Fin n → G) → A}
-- given
  (hx : (inhomogeneousCochains.d A n).hom x = 0)
  (h0 : x = 0) :
-- imply
  groupCohomology.π A n (groupCohomology.cocyclesMk x hx) = 0 := by
-- proof
  subst h0
  have h0' : groupCohomology.cocyclesMk (0 : (Fin n → G) → A) hx = 0 := by
    apply (ModuleCat.mono_iff_injective (groupCohomology.iCocycles A n)).mp inferInstance
    show (groupCohomology.iCocycles A n).hom (groupCohomology.cocyclesMk 0 hx) = (groupCohomology.iCocycles A n).hom 0
    rw [map_zero]
    exact groupCohomology.iCocycles_mk 0 hx
  rw [h0', map_zero]


-- created on 2026-10-05
