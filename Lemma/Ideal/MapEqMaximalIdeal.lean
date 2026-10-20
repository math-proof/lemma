import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry


universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_Scheme_Hom_map_stalkMap_maximalIdeal_eq_of_etale_restrict](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_map_stalkMap_maximalIdeal_eq_of_etale_restrict.lean)
-/
@[path]
private lemma main
    {X Y : Scheme.{u}} (f : X ⟶ Y) (W : X.Opens) [AlgebraicGeometry.Etale (W.ι ≫ f)] (x : X) (hx : x ∈ W) :
    Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f.base x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  classical
  let x' : (W : Scheme.{u}) := ⟨x, hx⟩
  have hxW : W.ι.base x' = x := rfl
  have key : Ideal.map ((W.ι ≫ f).stalkMap x').hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk ((W.ι ≫ f).base x'))) =
      IsLocalRing.maximalIdeal ((W : Scheme.{u}).presheaf.stalk x') := by
    algebraize [((W.ι ≫ f).stalkMap x').hom]
    have : IsLocalHom (algebraMap (Y.presheaf.stalk ((W.ι ≫ f).base x')) ((W : Scheme.{u}).presheaf.stalk x')) :=
      inferInstanceAs <| IsLocalHom ((W.ι ≫ f).stalkMap x').hom
    have : Algebra.EssFiniteType (Y.presheaf.stalk ((W.ι ≫ f).base x')) ((W : Scheme.{u}).presheaf.stalk x') := by
      rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
      exact LocallyOfFiniteType.stalkMap (W.ι ≫ f) x'
    have : Algebra.FormallyUnramified (Y.presheaf.stalk ((W.ι ≫ f).base x')) ((W : Scheme.{u}).presheaf.stalk x') := by
      rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
      exact FormallyUnramified.stalkMap (W.ι ≫ f) x'
    exact Algebra.FormallyUnramified.map_maximalIdeal
  simp only [Scheme.Hom.stalkMap_comp] at key
  change Ideal.map ((W.ι.stalkMap x').hom.comp (f.stalkMap x).hom) (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f.base x))) =
    IsLocalRing.maximalIdeal _ at key
  rw [← Ideal.map_map] at key
  let _ : IsIso (W.ι.stalkMap x') := inferInstance
  let E : X.presheaf.stalk x ≃+* (W : Scheme.{u}).presheaf.stalk x' := (asIso (W.ι.stalkMap x')).commRingCatIsoToRingEquiv
  have hcomp : (E.symm : (W : Scheme.{u}).presheaf.stalk x' →+* X.presheaf.stalk x).comp
      ((W.ι.stalkMap x').hom : X.presheaf.stalk x →+* (W : Scheme.{u}).presheaf.stalk x') = RingHom.id (X.presheaf.stalk x) :=
    RingHom.ext fun z => E.symm_apply_apply z
  have key2 := congrArg (Ideal.map (E.symm : (W : Scheme.{u}).presheaf.stalk x' →+* X.presheaf.stalk x)) key
  erw [Ideal.map_map, hcomp, Ideal.map_id] at key2
  let _ : IsLocalHom (E.symm : (W : Scheme.{u}).presheaf.stalk x' →+* X.presheaf.stalk x) :=
    ⟨fun a ha => by
      have h := ha.map E
      rwa [show E ((E.symm : (W : Scheme.{u}).presheaf.stalk x' →+* X.presheaf.stalk x) a) = a from E.apply_symm_apply a] at h⟩
  exact key2.trans (IsLocalRing.map_maximalIdeal_of_surjective
    (E.symm : (W : Scheme.{u}).presheaf.stalk x' →+* X.presheaf.stalk x) E.symm.surjective)


-- created on 2026-10-20
