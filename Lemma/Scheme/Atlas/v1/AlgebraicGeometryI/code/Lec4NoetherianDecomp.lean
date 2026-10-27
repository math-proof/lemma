import Mathlib
import Initialize.Tactic.Attr.Basic
open TopologicalSpace PrimeSpectrum Set


/--
[noetherian_finite_union_irreducible_components](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4NoetherianDecomp.lean)
-/
@[path]
lemma noetherian_finite_union_irreducible_components
  {X : Type*}
  [TopologicalSpace X]
  [NoetherianSpace X] :
-- imply
  (irreducibleComponents X).Finite ∧ ⋃₀ irreducibleComponents X = univ :=
-- proof
  ⟨NoetherianSpace.finite_irreducibleComponents, sUnion_irreducibleComponents⟩

/--
[noetherian_finite_union_closed_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4NoetherianDecomp.lean)
-/
@[path]
lemma noetherian_finite_union_closed_irreducible
  {X : Type*}
  [TopologicalSpace X]
  [NoetherianSpace X] :
-- imply
  ∃ S : Set (Set X), S.Finite ∧ (∀ t ∈ S, IsClosed t) ∧ (∀ t ∈ S, IsIrreducible t) ∧ ⋃₀ S = univ := by
-- proof
  obtain ⟨S, hf, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    (isClosed_univ (X := X))
  exact ⟨S, hf, hc, hi, hU.symm ▸ rfl⟩

/--
[vanishingIdeal_sUnion_finset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4NoetherianDecomp.lean)
-/
@[path]
lemma vanishingIdeal_sUnion_finset
  [CommRing R]
  {T : Finset (Set (PrimeSpectrum R))} :
-- imply
  vanishingIdeal (⋃₀ ↑T) = T.inf (vanishingIdeal ·) := by
-- proof
  induction T using Finset.cons_induction with
  | empty => simp [vanishingIdeal_empty]
  | cons a S haS ih =>
    rw [Finset.coe_cons, sUnion_insert, vanishingIdeal_union, Finset.inf_cons, ih]

/--
[radical_ideal_eq_finite_iInf_primes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4NoetherianDecomp.lean)
-/
@[path]
lemma radical_ideal_eq_finite_iInf_primes
  [CommRing R]
  [IsNoetherianRing R]
  {I : Ideal R}
-- given
  (hI : I.IsRadical) :
-- imply
  ∃ (S : Finset (Ideal R)), (∀ P ∈ S, Ideal.IsPrime P) ∧ I = S.inf id := by
-- proof
  obtain ⟨T, hTfin, _, hTirred, hTeq⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_zeroLocus (↑I : Set R))
  lift T to Finset (Set (PrimeSpectrum R)) using hTfin
  refine ⟨T.image vanishingIdeal, ?_, ?_⟩
  ·
    intro P hP
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hP
    exact isIrreducible_iff_vanishingIdeal_isPrime.mp (hTirred t (Finset.mem_coe.mpr ht))
  ·
    have hI_eq : I = vanishingIdeal (zeroLocus (↑I : Set R)) := by
      rw [vanishingIdeal_zeroLocus_eq_radical]; exact hI.radical.symm
    rw [hI_eq, hTeq, vanishingIdeal_sUnion_finset, Finset.inf_image]
    simp

/--
[closed_irreducible_iff_vanishingIdeal_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4NoetherianDecomp.lean)
-/
@[path]
lemma closed_irreducible_iff_vanishingIdeal_prime
  [CommRing R]
  {Z : Set (PrimeSpectrum R)}
-- given
  (_hZ : IsClosed Z) :
-- imply
  IsIrreducible Z ↔ (vanishingIdeal Z).IsPrime :=
-- proof
  isIrreducible_iff_vanishingIdeal_isPrime


-- created on 2026-10-23
