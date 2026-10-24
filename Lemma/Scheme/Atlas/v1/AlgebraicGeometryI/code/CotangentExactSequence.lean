import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CotangentExactSequence
open KaehlerDifferential
open scoped TensorProduct


/--
[conormalExactSeq_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CotangentExactSequence.lean)
-/
@[path]
lemma conormalExactSeq_exact
  {R : Type u}
  [CommRing R]
  [CommRing A]
  [CommRing B]
  [Algebra R A]
  [Algebra A B]
  [Algebra R B]
  [IsScalarTower R A B]
-- given
  (h : Function.Surjective (algebraMap A B)) :
-- imply
  Function.Exact (KaehlerDifferential.kerCotangentToTensor R A B) (KaehlerDifferential.mapBaseChange R A B) :=
-- proof
  KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h

/--
[conormalExactSeq_mapBaseChange_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CotangentExactSequence.lean)
-/
@[path]
lemma conormalExactSeq_mapBaseChange_surjective
  {R : Type u}
  [CommRing R]
  [CommRing A]
  [CommRing B]
  [Algebra R A]
  [Algebra A B]
  [Algebra R B]
  [IsScalarTower R A B]
-- given
  (h : Function.Surjective (algebraMap A B)) :
-- imply
  Function.Surjective (KaehlerDifferential.mapBaseChange R A B) :=
-- proof
  KaehlerDifferential.mapBaseChange_surjective R A B h

/--
[conormalExactSeq_rightExact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CotangentExactSequence.lean)
-/
@[path]
lemma conormalExactSeq_rightExact
  {R : Type u}
  [CommRing R]
  [CommRing A]
  [CommRing B]
  [Algebra R A]
  [Algebra A B]
  [Algebra R B]
  [IsScalarTower R A B]
-- given
  (h : Function.Surjective (algebraMap A B)) :
-- imply
  Function.Exact (KaehlerDifferential.kerCotangentToTensor R A B) (KaehlerDifferential.mapBaseChange R A B) ∧ Function.Surjective (KaehlerDifferential.mapBaseChange R A B) :=
-- proof
  ⟨KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h,
    KaehlerDifferential.mapBaseChange_surjective R A B h⟩

/--
[conormalExactSeq_shortExact_of_formallySmooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CotangentExactSequence.lean)
-/
@[path]
lemma conormalExactSeq_shortExact_of_formallySmooth
  {R : Type u}
  [CommRing R]
  [CommRing A]
  [CommRing B]
  [Algebra R A]
  [Algebra A B]
  [Algebra R B]
  [IsScalarTower R A B]
  [Algebra.FormallySmooth R A]
  [Algebra.FormallySmooth R B]
-- given
  (h : Function.Surjective (algebraMap A B)) :
-- imply
  Function.Injective (KaehlerDifferential.kerCotangentToTensor R A B) ∧ Function.Exact (KaehlerDifferential.kerCotangentToTensor R A B) (KaehlerDifferential.mapBaseChange R A B) ∧ Function.Surjective (KaehlerDifferential.mapBaseChange R A B) := by
-- proof
  refine ⟨?_, KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h,
    KaehlerDifferential.mapBaseChange_surjective R A B h⟩
  rw [Algebra.FormallySmooth.kerCotangentToTensor_injective_iff h]
  infer_instance

/--
[conormalExactSeq_splitInjection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CotangentExactSequence.lean)
-/
@[path]
lemma conormalExactSeq_splitInjection
  {R : Type u}
  [CommRing R]
  [CommRing A]
  [CommRing B]
  [Algebra R A]
  [Algebra A B]
  [Algebra R B]
  [IsScalarTower R A B]
  [Algebra.FormallySmooth R A]
  [Algebra.FormallySmooth R B]
-- given
  (h : Function.Surjective (algebraMap A B)) :
-- imply
  ∃ l : (B ⊗[A] Ω[A⁄R]) →ₗ[A] (RingHom.ker (algebraMap A B)).Cotangent, l ∘ₗ (KaehlerDifferential.kerCotangentToTensor R A B) = LinearMap.id :=
-- proof
  (Algebra.FormallySmooth.iff_split_injection h).mp inferInstance
/-- Dimension formula from the conormal short exact sequence: if `B ⊗_A Ω_{A/R}` has dimension
`n` and `Ω_{B/R}` has dimension `n - m`, then `I/I²` has dimension `m`. -/
section Corollary26
variable (R : Type u) [CommRing R]
variable {A B : Type*} [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/--
[conormalSequence_shortExact_of_smooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CotangentExactSequence.lean)
-/
@[path]
lemma conormalSequence_shortExact_of_smooth
  {R : Type u}
  [CommRing R]
  [CommRing A]
  [CommRing B]
  [Algebra R A]
  [Algebra A B]
  [Algebra R B]
  [IsScalarTower R A B]
  [Algebra.FormallySmooth R A]
  [Algebra.FormallySmooth R B]
-- given
  (h : Function.Surjective (algebraMap A B)) :
-- imply
  Function.Injective (KaehlerDifferential.kerCotangentToTensor R A B) ∧ Function.Exact (KaehlerDifferential.kerCotangentToTensor R A B) (KaehlerDifferential.mapBaseChange R A B) ∧ Function.Surjective (KaehlerDifferential.mapBaseChange R A B) := by
-- proof
  refine ⟨?_, KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R A B h,
    KaehlerDifferential.mapBaseChange_surjective R A B h⟩
  rw [Algebra.FormallySmooth.kerCotangentToTensor_injective_iff h]
  infer_instance
end Corollary26


-- created on 2026-10-23
