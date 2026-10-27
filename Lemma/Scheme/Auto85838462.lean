import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma isArtinianRing_top
  {k : Type u} [Field k] {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f] :
  IsArtinianRing (X.presheaf.obj (Opposite.op (⊤ : X.Opens))) := by
  have h := (HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := f)).mp inferInstance
  obtain ⟨_, hf⟩ := h
  let _ : Algebra ((Spec (CommRingCat.of k)).presheaf.obj (Opposite.op (⊤ : (Spec (CommRingCat.of k)).Opens))) (X.presheaf.obj (Opposite.op (⊤ : X.Opens))) := f.appTop.hom.toAlgebra
  let _ : Module.Finite ((Spec (CommRingCat.of k)).presheaf.obj (Opposite.op (⊤ : (Spec (CommRingCat.of k)).Opens))) (X.presheaf.obj (Opposite.op (⊤ : X.Opens))) := hf
  let _ : IsArtinianRing ((Spec (CommRingCat.of k)).presheaf.obj (Opposite.op (⊤ : (Spec (CommRingCat.of k)).Opens))) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective.isArtinianRing
  apply IsArtinianRing.of_finite ((Spec (CommRingCat.of k)).presheaf.obj (Opposite.op (⊤ : (Spec (CommRingCat.of k)).Opens))) (X.presheaf.obj (Opposite.op (⊤ : X.Opens)))

private lemma isField_stalk
  {k : Type u} [Field k] {X : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f] [IsReduced X] (x : X) :
  IsField (X.presheaf.stalk x) := by
  let _ : IsAffine X := isAffine_of_isAffineHom f
  let _ : IsArtinianRing (X.presheaf.obj (Opposite.op (⊤ : X.Opens))) := isArtinianRing_top f
  have hU : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  have hloc := hU.isLocalization_stalk ⟨x, trivial⟩
  let _ : Algebra (X.presheaf.obj (Opposite.op (⊤ : X.Opens))) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  let _ := hloc
  let _ : IsArtinianRing (X.presheaf.stalk x) :=
    IsArtinianRing.localization_artinian (R := X.presheaf.obj (Opposite.op (⊤ : X.Opens))) (S := (hU.primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl) (L := X.presheaf.stalk x)
  apply IsArtinianRing.isField_of_isReduced_of_isLocalRing (X.presheaf.stalk x)

/--
[AlgebraicGeometry_isReduced_of_isClosedImmersion_of_isFinite_of_isReduced](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isReduced_of_isClosedImmersion_of_isFinite_of_isReduced.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] {X Z : (Scheme : Type (u + 1))} (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f] [IsReduced X] (i : Z ⟶ X) [IsClosedImmersion i] :
  -- imply
  IsReduced Z := by
  -- proof
  let _ : ∀ z : Z, _root_.IsReduced (Z.presheaf.stalk z) := by
    intro z
    have hsurj : Function.Surjective (i.stalkMap z).hom := i.stalkMap_surjective z
    let _ := (isField_stalk f (i.base z)).toField
    have hinj : Function.Injective (i.stalkMap z).hom := (i.stalkMap z).hom.injective
    let e := RingEquiv.ofBijective (i.stalkMap z).hom ⟨hinj, hsurj⟩
    apply isReduced_of_injective e.symm e.symm.injective
  apply isReduced_of_isReduced_stalk Z


-- created on 2026-10-20
