import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_LocallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_LocallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective.lean)
-/
@[path]
private lemma main
  {X Y Z : (Scheme : Type (u + 1))} (f : X ⟶ Y) (g : Y ⟶ Z)
  [LocallyOfFiniteType (f ≫ g)] [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Z] :
  LocallyOfFiniteType g := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFiniteType)]
  intro U V e
  have hV' : IsAffineOpen ((TopologicalSpace.Opens.map f.base).obj (V : Y.Opens) : X.Opens) :=
    V.2.preimage f
  let V' : X.affineOpens := ⟨(TopologicalSpace.Opens.map f.base).obj (V : Y.Opens), hV'⟩
  have e' : (V' : X.Opens) ≤ ((TopologicalSpace.Opens.map (f ≫ g).base).obj (U : Z.Opens) : X.Opens) :=
    ((TopologicalSpace.Opens.map f.base).map (homOfLE e)).le
  let φAB := g.appLE U V e
  let φBC := f.appLE V V' le_rfl
  let φAC := (f ≫ g).appLE U V' e'
  have hcomp : φAB ≫ φBC = φAC := Scheme.Hom.appLE_comp_appLE f g U V V' e le_rfl
  have hAC : φAC.hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) _ ‹_› U V' e'
  have hBC : φBC.hom.Finite := by
    have := IsFinite.finite_app f V V.2
    rwa [Scheme.Hom.app_eq_appLE] at this
  have hBCflat : φBC.hom.Flat := HasRingHomProperty.appLE (P := @Flat) _ ‹_› V V' le_rfl
  have hBCsurj : Surjective (Spec.map φBC) := by
    refine ⟨fun q => ?_⟩
    have hq : (V.2.fromSpec q : Y) ∈ (V : Y.Opens) :=
      V.2.range_fromSpec.le (Set.mem_range_self q)
    obtain ⟨x, hx⟩ := ‹Surjective f›.surj (V.2.fromSpec q)
    have hxV' : x ∈ (V' : X.Opens) := by
      show f x ∈ (V : Y.Opens)
      rw [hx]
      apply hq
    obtain ⟨p, hp⟩ := hV'.range_fromSpec.ge hxV'
    refine ⟨p, V.2.fromSpec.isOpenEmbedding.injective ?_⟩
    have key := congrArg (fun h ↦ h p) (IsAffineOpen.SpecMap_appLE_fromSpec f V.2 hV' le_rfl)
    simp only [Scheme.Hom.comp_apply] at key
    change V.2.fromSpec (Spec.map φBC p) = V.2.fromSpec q
    rw [key, hp, hx]
  have hBCinj : Function.Injective φBC.hom :=
    ((flat_and_surjective_SpecMap_iff φBC).mp
      ⟨(HasRingHomProperty.Spec_iff (P := @Flat)).mpr hBCflat, hBCsurj⟩).injective
  algebraize [φAB.hom, φBC.hom, φAC.hom]
  have htower : (φAC.hom : (Z.presheaf.obj (Opposite.op U)) →+* X.presheaf.obj (Opposite.op (V' : X.Opens))) =
      φBC.hom.comp φAB.hom := by
    rw [← hcomp]
    rfl
  have : IsScalarTower (Z.presheaf.obj (Opposite.op U)) (Y.presheaf.obj (Opposite.op V))
    (X.presheaf.obj (Opposite.op (V' : X.Opens))) :=
    .of_algebraMap_eq' htower
  have : IsNoetherianRing (Z.presheaf.obj (Opposite.op U)) := IsLocallyNoetherian.component_noetherian U
  have hfg := fg_of_fg_of_fg (Z.presheaf.obj (Opposite.op U)) (Y.presheaf.obj (Opposite.op V))
    (X.presheaf.obj (Opposite.op (V' : X.Opens))) hAC.out Module.Finite.fg_top hBCinj
  refine ⟨hfg⟩


-- created on 2026-10-20
