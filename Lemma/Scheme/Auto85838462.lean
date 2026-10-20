import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma isArtinianRing_top {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f] :
    IsArtinianRing Γ(X, ⊤) := by
  have h := (HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := f)).mp inferInstance
  obtain ⟨_, hf⟩ := h
  let _ : Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let _ : Module.Finite Γ(Spec (CommRingCat.of k), ⊤) Γ(X, ⊤) := hf
  let _ : IsArtinianRing Γ(Spec (CommRingCat.of k), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective.isArtinianRing
  exact IsArtinianRing.of_finite Γ(Spec (CommRingCat.of k), ⊤) Γ(X, ⊤)
private lemma isField_stalk {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f]
    [IsReduced X] (x : X) : IsField (X.presheaf.stalk x) := by
  let _ : IsAffine X := isAffine_of_isAffineHom f
  let _ : IsArtinianRing Γ(X, ⊤) := isArtinianRing_top f
  have hU : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  have hloc := hU.isLocalization_stalk ⟨x, trivial⟩
  let _ : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  let _ := hloc
  let _ : IsArtinianRing (X.presheaf.stalk x) :=
    IsArtinianRing.localization_artinian (R := Γ(X, ⊤)) (S := (hU.primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl)
      (L := X.presheaf.stalk x)
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing (X.presheaf.stalk x)
/--
[AlgebraicGeometry_isReduced_of_isClosedImmersion_of_isFinite_of_isReduced](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isReduced_of_isClosedImmersion_of_isFinite_of_isReduced.lean)
-/
@[path]
private lemma main
    {k : Type u} [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f] [IsReduced X]
    (i : Z ⟶ X) [IsClosedImmersion i] : IsReduced Z := by
  let _ : ∀ z : Z, _root_.IsReduced (Z.presheaf.stalk z) := by
    intro z
    have hsurj : Function.Surjective (i.stalkMap z).hom := i.stalkMap_surjective z
    let _ := (isField_stalk f (i.base z)).toField
    have hinj : Function.Injective (i.stalkMap z).hom := (i.stalkMap z).hom.injective
    let e := RingEquiv.ofBijective (i.stalkMap z).hom ⟨hinj, hsurj⟩
    exact isReduced_of_injective e.symm e.symm.injective
  exact isReduced_of_isReduced_stalk Z

-- created on 2026-10-20
