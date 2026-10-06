import Mathlib
import sympy.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopologicalSpace Opposite
open TopCat TopCat.Presheaf

/--
[AlgebraicGeometry_bijective_app_of_forall_isAffineOpen](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_bijective_app_of_forall_isAffineOpen.lean)
-/

private lemma  stalkFunctor_map_surjective_of_isBasis {X : TopCat.{u}} {B : Set (Opens X)} (hB : Opens.IsBasis B)
    {F G : X.Presheaf CommRingCat.{u}} {α : F ⟶ G} (hα : ∀ U ∈ B, Function.Surjective (α.app (op U))) (x : X) :
    Function.Surjective ((stalkFunctor _ x).map α) := by
  intro t
  obtain ⟨U, hxU, hU, t, rfl⟩ := exists_mem_germ_eq_of_isBasis hB G x t
  obtain ⟨s, rfl⟩ := hα U hU t
  exact ⟨F.germ U x hxU s, by rw [stalkFunctor_map_germ_apply]⟩
@[main]
private lemma main
  {X B : Scheme.{u}}
  {p : X ⟶ B}
  {U : B.Opens}
-- given
  (h : ∀ U : B.Opens, IsAffineOpen U → Function.Bijective (p.app U)) :
-- imply
  Function.Bijective (p.app U) := by
-- proof
  let F : TopCat.Sheaf CommRingCat.{u} B.carrier := B.sheaf
  let G : TopCat.Sheaf CommRingCat.{u} B.carrier := (TopCat.Sheaf.pushforward _ p.base).obj X.sheaf
  let f : F ⟶ G := ⟨p.c⟩
  have key := TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective f U (fun x _ =>
    ⟨TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis B.isBasis_affineOpens
        (fun V hV => (h V hV).1) x,
     stalkFunctor_map_surjective_of_isBasis B.isBasis_affineOpens
        (fun V hV => (h V hV).2) x⟩)
  exact key


-- created on 2026-10-05
