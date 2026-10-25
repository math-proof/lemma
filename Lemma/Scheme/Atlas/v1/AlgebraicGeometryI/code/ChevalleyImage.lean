import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.ChevalleyImage
open PrimeSpectrum Topology


/--
[dense_constructible_contains_basicOpen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyImage.lean)
-/
@[path]
lemma dense_constructible_contains_basicOpen
  [CommRing R]
  [IsDomain R]
  {s : Set (PrimeSpectrum R)}
-- given
  (hs : IsConstructible s)
  (hd : Dense s) :
-- imply
  ∃ b : R, b ≠ 0 ∧ (↑(basicOpen b) : Set (PrimeSpectrum R)) ⊆ s := by
-- proof
  obtain ⟨S, rfl⟩ := exists_constructibleSetData_iff.mpr hs
  set η : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : η ∈ closure S.toSet := hd.closure_eq ▸ Set.mem_univ _
  rw [show S.toSet = ⋃ C ∈ S, C.toSet from rfl, S.closure_biUnion _] at hη
  simp only [Set.mem_iUnion] at hη
  obtain ⟨C, hC, hηC⟩ := hη
  have hclosed : closure C.toSet ⊆ zeroLocus (Set.range C.g) :=
    closure_minimal Set.diff_subset (isClosed_zeroLocus _)
  have hη_in_V : Set.range C.g ⊆ ↑η.asIdeal := hclosed hηC
  have hg_zero : ∀ j, C.g j = 0 := by
    intro j; have := hη_in_V (Set.mem_range_self j); simp [η] at this; exact this
  have hV_univ : zeroLocus (Set.range C.g) = Set.univ := by
    rw [zeroLocus_eq_univ_iff]; rintro _ ⟨j, rfl⟩; rw [hg_zero j]; exact zero_mem _
  have hC_eq : C.toSet = ↑(basicOpen C.f) := by
    show zeroLocus (Set.range C.g) \ zeroLocus {C.f} = _
    rw [hV_univ]; ext x; simp [basicOpen, zeroLocus, Set.mem_diff]
  have hne : C.toSet.Nonempty := by
    by_contra h; rw [Set.not_nonempty_iff_eq_empty] at h; simp [h] at hηC
  rw [hC_eq] at hne
  have hb_ne : C.f ≠ 0 := by
    intro h; rw [h, basicOpen_zero] at hne; exact hne.ne_empty rfl
  exact ⟨C.f, hb_ne, by rw [← hC_eq]; exact fun x hx => Set.mem_biUnion hC hx⟩

/--
[denseRange_comap_of_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyImage.lean)
-/
@[path]
lemma denseRange_comap_of_injective
  [CommRing B]
  [CommRing A]
  [IsDomain B]
  [Algebra B A]
-- given
  (hf : Function.Injective (algebraMap B A)) :
-- imply
  DenseRange (PrimeSpectrum.comap (algebraMap B A)) := by
-- proof
  rw [denseRange_comap_iff_ker_le_nilRadical]
  intro x hx; rw [RingHom.mem_ker] at hx
  rw [show x = 0 from hf (by rw [hx, map_zero])]; exact zero_mem _

/--
[chevalley_algebraic_core](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyImage.lean)
-/
@[path]
lemma chevalley_algebraic_core
  {B A : Type*}
  [CommRing B]
  [CommRing A]
  [IsDomain B]
  [IsDomain A]
  [IsNoetherianRing B]
  [Algebra B A]
  [Algebra.FiniteType B A]
-- given
  (hf : Function.Injective (algebraMap B A)) :
-- imply
  ∃ b : B, b ≠ 0 ∧ (↑(basicOpen b) : Set (PrimeSpectrum B)) ⊆ Set.range (PrimeSpectrum.comap (algebraMap B A)) :=
-- proof
  dense_constructible_contains_basicOpen
    (isConstructible_range_comap
      (RingHom.finitePresentation_algebraMap.mpr
        (Algebra.FinitePresentation.of_finiteType.mp ‹_›)))
    (denseRange_comap_of_injective hf)

/--
[chevalley_algebraic_core_primes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyImage.lean)
-/
@[path]
lemma chevalley_algebraic_core_primes
  {B A : Type*}
  [CommRing B]
  [CommRing A]
  [IsDomain B]
  [IsDomain A]
  [IsNoetherianRing B]
  [Algebra B A]
  [Algebra.FiniteType B A]
-- given
  (hf : Function.Injective (algebraMap B A)) :
-- imply
  ∃ b : B, b ≠ 0 ∧ ∀ (𝔮 : Ideal B) [𝔮.IsPrime], b ∉ 𝔮 → ∃ (𝔭 : Ideal A), 𝔭.IsPrime ∧ 𝔭.comap (algebraMap B A) = 𝔮 := by
-- proof
  obtain ⟨b, hb, hD⟩ := chevalley_algebraic_core B A hf
  refine ⟨b, hb, fun 𝔮 h𝔮 hb𝔮 => ?_⟩
  have hq : (⟨𝔮, h𝔮⟩ : PrimeSpectrum B) ∈ (↑(basicOpen b) : Set (PrimeSpectrum B)) := by
    simp [basicOpen]; exact hb𝔮
  obtain ⟨p, hp⟩ := hD hq
  exact ⟨p.asIdeal, p.isPrime, congr_arg PrimeSpectrum.asIdeal hp⟩

/--
[chevalley_image_contains_dense_open](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyImage.lean)
-/
@[path]
lemma chevalley_image_contains_dense_open
  {B A : Type*}
  [CommRing B]
  [CommRing A]
  [IsDomain B]
  [IsDomain A]
  [IsNoetherianRing B]
  [Algebra B A]
  [Algebra.FiniteType B A]
-- given
  (hf : Function.Injective (algebraMap B A)) :
-- imply
  ∃ (U : TopologicalSpace.Opens (PrimeSpectrum B)), (U : Set (PrimeSpectrum B)).Nonempty ∧ Dense (U : Set (PrimeSpectrum B)) ∧ (U : Set (PrimeSpectrum B)) ⊆ Set.range (PrimeSpectrum.comap (algebraMap B A)) := by
-- proof
  obtain ⟨b, hb, hD⟩ := chevalley_algebraic_core B A hf
  haveI : IrreducibleSpace (PrimeSpectrum B) := irreducibleSpace
  refine ⟨basicOpen b, ?_, ?_, hD⟩
  · exact ⟨⟨⊥, Ideal.isPrime_bot⟩, by simp [hb]⟩
  · exact IsOpen.dense isOpen_basicOpen ⟨⟨⊥, Ideal.isPrime_bot⟩, by simp [hb]⟩

/--
[chevalley_constructible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyImage.lean)
-/
@[path]
lemma chevalley_constructible
  {B A : Type*}
  [CommRing B]
  [CommRing A]
  [IsNoetherianRing B]
  [Algebra B A]
  [Algebra.FiniteType B A] :
-- imply
  IsConstructible (Set.range (PrimeSpectrum.comap (algebraMap B A))) :=
-- proof
  isConstructible_range_comap
    (RingHom.finitePresentation_algebraMap.mpr
      (Algebra.FinitePresentation.of_finiteType.mp ‹_›))

/--
[chevalley_open_map_of_flat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyImage.lean)
-/
@[path]
lemma chevalley_open_map_of_flat
  {B A : Type*}
  [CommRing B]
  [CommRing A]
  [IsNoetherianRing B]
  [Algebra B A]
  [Algebra.FiniteType B A]
  [Module.Flat B A] :
-- imply
  IsOpenMap (PrimeSpectrum.comap (algebraMap B A)) := by
-- proof
  have : Algebra.FinitePresentation B A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  exact isOpenMap_comap_of_hasGoingDown_of_finitePresentation


-- created on 2026-10-23
