import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Fiber
import Lemma.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits NeronModelInfra

universe u

namespace AlgebraicGeometry

instance SmoothOfRelativeDimension.smooth_one {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 1 f

instance SmoothOfRelativeDimension.pullback_snd (n : ℕ) {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [SmoothOfRelativeDimension n f] : SmoothOfRelativeDimension n (pullback.snd f g) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange n
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) f g inferInstance

instance SmoothOfRelativeDimension.pullback_fst (n : ℕ) {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [SmoothOfRelativeDimension n g] : SmoothOfRelativeDimension n (pullback.fst f g) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange n
  MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension n) f g inferInstance

instance SmoothOfRelativeDimension.fiberToSpecResidueField (n : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension n f] (s : S) : SmoothOfRelativeDimension n (f.fiberToSpecResidueField s) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange n
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) _ _ inferInstance

instance IsProper.fiberToSpecResidueField {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s : S) :
    IsProper (f.fiberToSpecResidueField s) :=
  MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance

namespace SmoothProperCurve

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))

section BaseChange

variable (T : Type u) [CommRing T] [Algebra R T]

abbrev specMap : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R T))

abbrev baseChange : pullback c (specMap R T) ⟶ Spec (CommRingCat.of T) :=
  pullback.snd c (specMap R T)

example [SmoothOfRelativeDimension 1 c] : SmoothOfRelativeDimension 1 (baseChange R c T) :=
  inferInstance
example [IsProper c] : IsProper (baseChange R c T) := inferInstance
example [GeometricallyIntegral c] : GeometricallyIntegral (baseChange R c T) := inferInstance

variable {R c}

def sectionBaseChange (ε : SchemeHomOver (𝟙 _) c) : SchemeHomOver (𝟙 _) (baseChange R c T) :=
  ⟨pullback.lift (specMap R T ≫ ε.1) (𝟙 _) (by rw [Category.assoc, ε.2]; simp),
    pullback.lift_snd _ _ _⟩

@[simp]
theorem sectionBaseChange_coe_fst (ε : SchemeHomOver (𝟙 _) c) :
    (sectionBaseChange T ε).1 ≫ pullback.fst c (specMap R T) = specMap R T ≫ ε.1 :=
  pullback.lift_fst _ _ _

@[simp]
theorem sectionBaseChange_coe_snd (ε : SchemeHomOver (𝟙 _) c) :
    (sectionBaseChange T ε).1 ≫ pullback.snd c (specMap R T) = 𝟙 _ :=
  pullback.lift_snd _ _ _

end BaseChange

instance isIntegral_pullback_Spec_field [GeometricallyIntegral c] {K : Type u} [Field K]
    (ξ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) : IsIntegral (pullback c ξ) :=
  GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback c ξ)

example [GeometricallyIntegral c] (K : Type u) [Field K] [Algebra R K] :
    IsIntegral (pullback c (specMap R K)) := inferInstance

end SmoothProperCurve

end AlgebraicGeometry

end
