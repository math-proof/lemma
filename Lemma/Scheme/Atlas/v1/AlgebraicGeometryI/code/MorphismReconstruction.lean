import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.MorphismReconstruction
open AlgebraicGeometry CategoryTheory


/--
[normal_variety_is_integral_closure_of_function_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MorphismReconstruction.lean)
-/
@[path]
lemma normal_variety_is_integral_closure_of_function_field
  {B A : Type*}
  [CommRing B]
  [IsDomain B]
  [CommRing A]
  [IsDomain A]
  [Algebra B A]
  [Algebra.IsIntegral B A]
  [IsIntegrallyClosed A] :
-- imply
  IsIntegralClosure A B (FractionRing A) := by
-- proof
  have : IsScalarTower B A (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  constructor
  ·
    exact IsFractionRing.injective A (FractionRing A)
  · intro x
    constructor
    ·
      intro hx
      have hxA : IsIntegral A x := hx.tower_top
      exact (isIntegrallyClosed_iff (FractionRing A)).mp inferInstance hxA
    ·
      rintro ⟨y, rfl⟩
      exact (Algebra.IsIntegral.isIntegral (R := B) y).algebraMap

/--
[normal_variety_reconstruction_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MorphismReconstruction.lean)
-/
@[path]
lemma normal_variety_reconstruction_unique
  {B A A' K : Type*}
  [CommRing B]
  [IsDomain B]
  [CommRing A]
  [IsDomain A]
  [CommRing A']
  [IsDomain A']
  [CommRing K]
  [Algebra B K]
  [Algebra B A]
  [Algebra.IsIntegral B A]
  [IsIntegrallyClosed A]
  [Algebra A K]
  [IsScalarTower B A K]
  [Algebra B A']
  [Algebra.IsIntegral B A']
  [IsIntegrallyClosed A']
  [Algebra A' K]
  [IsScalarTower B A' K]
  [IsFractionRing A K]
  [IsFractionRing A' K] :
-- imply
  Nonempty (A ≃ₐ[B] A') := by
-- proof
  have hA : IsIntegralClosure A B K := by
    constructor
    · exact IsFractionRing.injective A K
    · intro x
      constructor
      · intro hx
        exact (isIntegrallyClosed_iff K).mp inferInstance hx.tower_top
      · rintro ⟨y, rfl⟩
        exact (Algebra.IsIntegral.isIntegral (R := B) y).algebraMap
  have hA' : IsIntegralClosure A' B K := by
    constructor
    · exact IsFractionRing.injective A' K
    · intro x
      constructor
      · intro hx
        exact (isIntegrallyClosed_iff K).mp inferInstance hx.tower_top
      · rintro ⟨y, rfl⟩
        exact (Algebra.IsIntegral.isIntegral (R := B) y).algebraMap
  exact ⟨IsIntegralClosure.equiv B A K A'⟩

/--
[corollary22_scheme_iso_over_base](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MorphismReconstruction.lean)
-/
@[path]
lemma corollary22_scheme_iso_over_base
  {B A A' K : Type}
  [CommRing B]
  [IsDomain B]
  [CommRing A]
  [IsDomain A]
  [CommRing A']
  [IsDomain A']
  [CommRing K]
  [Algebra B K]
  [Algebra B A]
  [Algebra.IsIntegral B A]
  [IsIntegrallyClosed A]
  [Algebra A K]
  [IsScalarTower B A K]
  [Algebra B A']
  [Algebra.IsIntegral B A']
  [IsIntegrallyClosed A']
  [Algebra A' K]
  [IsScalarTower B A' K]
  [IsFractionRing A K]
  [IsFractionRing A' K] :
-- imply
  (corollary22_scheme_iso B A A' K).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B A)) = Spec.map (CommRingCat.ofHom (algebraMap B A')) := by
-- proof
  unfold corollary22_scheme_iso
  simp only [Functor.mapIso_hom]
  change Spec.map (CommRingCat.ofHom (IsIntegralClosure.equiv B A K A').toAlgHom.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap B A)) =
    Spec.map (CommRingCat.ofHom (algebraMap B A'))
  rw [← Spec.map_comp]
  congr 1
  ext (x : B)
  simp [AlgEquiv.commutes]


-- created on 2026-10-23
