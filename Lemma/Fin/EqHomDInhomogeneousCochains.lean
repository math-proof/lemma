import Mathlib
import sympy.Basic

open CategoryTheory groupCohomology

/--
[groupCohomology_inhomogeneousCochains_d_comp_apply](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_inhomogeneousCochains_d_comp_apply.lean)
-/
@[main]
private lemma main
  {k G : Type} [CommRing k] [Group G]
  {A B : Rep.{0} k G}
  {φ : A ⟶ B}
  {n : ℕ}
  {x : (Fin n → G) → A} :
-- imply
  ((inhomogeneousCochains B).d n (n + 1)).hom (fun g => φ.hom (x g)) =
      fun g => φ.hom (((inhomogeneousCochains A).d n (n + 1)).hom x g) := by
-- proof
  have h := (cochainsMap (MonoidHom.id G) φ).comm n (n + 1)

  have h2 := congrArg (fun T => (ModuleCat.Hom.hom T) x) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, cochainsMap_id_f_hom_eq_compLeft] at h2
  exact h2


-- created on 2026-10-05
