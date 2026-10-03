import Mathlib
import sympy.Basic

open CategoryTheory groupCohomology

/--
[groupCohomology_pi_cocyclesMk_zsmul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_pi_cocyclesMk_zsmul.lean)
-/
@[main]
private lemma main
  [Group G]
  {A : Rep.{0} ℤ G}
  {n : ℕ}
  {m : ℤ}
  {x : (Fin n → G) → A}
-- given
  (hx : (inhomogeneousCochains.d A n).hom x = 0)
  (hmx : (inhomogeneousCochains.d A n).hom (m • x) = 0) :
-- imply
  groupCohomology.π A n (groupCohomology.cocyclesMk (m • x) hmx) = m • groupCohomology.π A n (groupCohomology.cocyclesMk x hx) := by
-- proof
  have h : groupCohomology.cocyclesMk (m • x) hmx = m • groupCohomology.cocyclesMk x hx := by
    apply (ModuleCat.mono_iff_injective (iCocycles A n)).1 inferInstance
    rw [map_zsmul, iCocycles_mk, iCocycles_mk]
  rw [h, map_zsmul]


-- created on 2026-10-03
