import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec20ConormalSequence
open AlgebraicGeometry CategoryTheory KaehlerDifferential


/--
[closedImmersion_stalkMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20ConormalSequence.lean)
-/
@[path]
lemma closedImmersion_stalkMap_surjective
  {X Z : Scheme.{u}}
  {i : Z ⟶ X}
  [IsClosedImmersion i]
  {z : Z} :
-- imply
  Function.Surjective (i.stalkMap z).hom :=
-- proof
  SurjectiveOnStalks.stalkMap_surjective i z

/--
[conormalSequence_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20ConormalSequence.lean)
-/
@[path]
lemma conormalSequence_exact
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  {B : Type u}
  [CommRing B]
  [Algebra R B]
  [Algebra A B]
  [IsScalarTower R A B]
-- given
  (hsurj : Function.Surjective (algebraMap A B)) :
-- imply
  LinearMap.range (kerCotangentToTensor R A B) = (LinearMap.ker (mapBaseChange R A B)).restrictScalars A :=
-- proof
  range_kerCotangentToTensor R A B hsurj

/--
[conormalSequence_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20ConormalSequence.lean)
-/
@[path]
lemma conormalSequence_surjective
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  {B : Type u}
  [CommRing B]
  [Algebra R B]
  [Algebra A B]
  [IsScalarTower R A B] :
-- imply
  Function.Surjective (KaehlerDifferential.map R A B B) :=
-- proof
  KaehlerDifferential.map_surjective R A B

/--
[jacobiZariski_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20ConormalSequence.lean)
-/
@[path]
lemma jacobiZariski_exact
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  {B : Type u}
  [CommRing B]
  [Algebra R B]
  [Algebra A B]
  [IsScalarTower R A B] :
-- imply
  Function.Exact (mapBaseChange R A B) (KaehlerDifferential.map R A B B) :=
-- proof
  exact_mapBaseChange_map R A B
section ConormalPart2

/--
[conormalSequence_injective_iff_h1Cotangent_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20ConormalSequence.lean)
-/
@[path]
lemma conormalSequence_injective_iff_h1Cotangent_subsingleton
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  [Algebra.FormallySmooth R A]
  {B : Type u}
  [CommRing B]
  [Algebra R B]
  [Algebra A B]
  [IsScalarTower R A B]
-- given
  (hsurj : Function.Surjective (algebraMap A B)) :
-- imply
  Function.Injective (kerCotangentToTensor R A B) ↔ Subsingleton (Algebra.H1Cotangent R B) :=
-- proof
  Algebra.FormallySmooth.kerCotangentToTensor_injective_iff hsurj

/--
[conormalSequence_injective_of_formallySmooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20ConormalSequence.lean)
-/
@[path]
lemma conormalSequence_injective_of_formallySmooth
  {R : Type u}
  [CommRing R]
  {A : Type u}
  [CommRing A]
  [Algebra R A]
  [Algebra.FormallySmooth R A]
  {P : Algebra.Extension R A}
  [Algebra.FormallySmooth R P.Ring] :
-- imply
  Function.Injective P.cotangentComplex := by
-- proof
  rwa [P.cotangentComplex_injective_iff]

/--
[conormalSequence_ses_iff_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20ConormalSequence.lean)
-/
@[path]
lemma conormalSequence_ses_iff_smooth
  {X Z S : Scheme.{u}}
  {i : Z ⟶ X}
  [IsClosedImmersion i]
  {f : X ⟶ S}
  [Smooth f]
  [IsNoetherian X]
  {z : Z} :
-- imply
  ((i ≫ f).stalkMap z).hom.FormallySmooth ↔ z ∈ (i ≫ f).smoothLocus := by
-- proof
  rw [Scheme.Hom.mem_smoothLocus]
end ConormalPart2
section ConormalPart3

/--
[conormalSequence_smoothLocus_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20ConormalSequence.lean)
-/
@[path]
lemma conormalSequence_smoothLocus_isOpen
  {X Z S : Scheme.{u}}
  {i : Z ⟶ X}
  [IsClosedImmersion i]
  {f : X ⟶ S}
  [Smooth f]
  [IsNoetherian X] :
-- imply
  IsOpen {z : Z | ((i ≫ f).stalkMap z).hom.FormallySmooth} :=
-- proof
  Scheme.Hom.isOpen_smoothLocus (i ≫ f)

/--
[conormalSequence_smoothness_propagates](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20ConormalSequence.lean)
-/
@[path]
lemma conormalSequence_smoothness_propagates
  {X Z S : Scheme.{u}}
  {i : Z ⟶ X}
  [IsClosedImmersion i]
  {f : X ⟶ S}
  [Smooth f]
  [IsNoetherian X]
  {z₀ : Z}
-- given
  (hz₀ : ((i ≫ f).stalkMap z₀).hom.FormallySmooth) :
-- imply
  ∃ (U : TopologicalSpace.Opens Z), z₀ ∈ U ∧ ∀ z ∈ U, ((i ≫ f).stalkMap z).hom.FormallySmooth := by
-- proof
  have hopen := conormalSequence_smoothLocus_isOpen i f
  exact ⟨⟨{z | ((i ≫ f).stalkMap z).hom.FormallySmooth}, hopen⟩, hz₀, fun z hz => hz⟩
end ConormalPart3


-- created on 2026-10-23
