import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.RadicalIdealCorrespondence
open PrimeSpectrum Ideal


/--
[gc_zeroLocus_vanishingIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma gc_zeroLocus_vanishingIdeal
  {R : Type*}
  [CommSemiring R] :
-- imply
  @GaloisConnection (Ideal R) (Set (PrimeSpectrum R))ᵒᵈ _ _ (fun I => PrimeSpectrum.zeroLocus I) fun t => PrimeSpectrum.vanishingIdeal t :=
-- proof
  PrimeSpectrum.gc R

/--
[abstract_nullstellensatz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma abstract_nullstellensatz
  {R : Type*}
  [CommSemiring R]
  {I : Ideal R} :
-- imply
  PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (I : Set R)) = I.radical :=
-- proof
  PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical I

/--
[vanishingIdeal_zeroLocus_of_isRadical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma vanishingIdeal_zeroLocus_of_isRadical
  {R : Type*}
  [CommSemiring R]
  {I : Ideal R}
-- given
  (hI : I.IsRadical) :
-- imply
  PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (I : Set R)) = I := by
-- proof
  rw [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hI.radical]

/--
[zeroLocus_vanishingIdeal_eq_closure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma zeroLocus_vanishingIdeal_eq_closure
  {R : Type*}
  [CommSemiring R]
  {t : Set (PrimeSpectrum R)} :
-- imply
  PrimeSpectrum.zeroLocus ↑(PrimeSpectrum.vanishingIdeal t) = closure t :=
-- proof
  PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure t

/--
[zeroLocus_eq_iff_radical_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma zeroLocus_eq_iff_radical_eq
  {R : Type*}
  [CommSemiring R]
  {I J : Ideal R} :
-- imply
  PrimeSpectrum.zeroLocus (I : Set R) = PrimeSpectrum.zeroLocus J ↔ I.radical = J.radical :=
-- proof
  PrimeSpectrum.zeroLocus_eq_iff

/--
[isRadical_vanishingIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma isRadical_vanishingIdeal
  {R : Type*}
  [CommSemiring R]
  {s : Set (PrimeSpectrum R)} :
-- imply
  (PrimeSpectrum.vanishingIdeal s).IsRadical :=
-- proof
  PrimeSpectrum.isRadical_vanishingIdeal s

/--
[nullstellensatz_galois_connection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma nullstellensatz_galois_connection
  [Field k]
  [Field K]
  [Algebra k K] :
-- imply
  @GaloisConnection (Ideal (MvPolynomial σ k)) (Set (σ → K))ᵒᵈ _ _ (MvPolynomial.zeroLocus K) (MvPolynomial.vanishingIdeal k) :=
-- proof
  MvPolynomial.zeroLocus_vanishingIdeal_galoisConnection

/--
[nullstellensatz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma nullstellensatz
  [Field k]
  [Field K]
  [Algebra k K]
  [IsAlgClosed K]
  [Finite σ]
  {I : Ideal (MvPolynomial σ k)} :
-- imply
  MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus K I) = I.radical :=
-- proof
  MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I

/--
[nullstellensatz_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma nullstellensatz_prime
  [Field k]
  [Field K]
  [Algebra k K]
  [IsAlgClosed K]
  [Finite σ]
  {P : Ideal (MvPolynomial σ k)}
  [hP : P.IsPrime] :
-- imply
  MvPolynomial.vanishingIdeal k (MvPolynomial.zeroLocus K P) = P :=
-- proof
  MvPolynomial.IsPrime.vanishingIdeal_zeroLocus P

/--
[weak_nullstellensatz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma weak_nullstellensatz
  [Field k]
  [Field K]
  [Algebra k K]
  [IsAlgClosed K]
  [Finite σ]
  {I : Ideal (MvPolynomial σ k)}
-- given
  (hI : I.IsMaximal) :
-- imply
  ∃ x : σ → K, I = MvPolynomial.vanishingIdeal k {x} :=
-- proof
  MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hI
section IrreducibilityAndPrimes
variable {R : Type*} [CommSemiring R]

/--
[irreducible_zeroLocus_iff_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma irreducible_zeroLocus_iff_prime
  [CommSemiring R]
  {I : Ideal R} :
-- imply
  IsIrreducible (PrimeSpectrum.zeroLocus (I : Set R)) ↔ I.radical.IsPrime :=
-- proof
  PrimeSpectrum.isIrreducible_zeroLocus_iff I

/--
[irreducible_zeroLocus_iff_prime_of_radical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma irreducible_zeroLocus_iff_prime_of_radical
  [CommSemiring R]
  {I : Ideal R}
-- given
  (hI : I.IsRadical) :
-- imply
  IsIrreducible (PrimeSpectrum.zeroLocus (I : Set R)) ↔ I.IsPrime :=
-- proof
  PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical I hI

/--
[isIrreducible_iff_vanishingIdeal_isPrime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma isIrreducible_iff_vanishingIdeal_isPrime
  [CommSemiring R]
  {s : Set (PrimeSpectrum R)} :
-- imply
  IsIrreducible s ↔ (PrimeSpectrum.vanishingIdeal s).IsPrime :=
-- proof
  PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime

/--
[vanishingIdeal_irreducible_eq_primes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma vanishingIdeal_irreducible_eq_primes
  [CommSemiring R] :
-- imply
  PrimeSpectrum.vanishingIdeal (R := R) '' {s | IsIrreducible s} = {P | P.IsPrime} :=
-- proof
  PrimeSpectrum.vanishingIdeal_isIrreducible

/--
[vanishingIdeal_closed_irreducible_eq_primes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma vanishingIdeal_closed_irreducible_eq_primes
  [CommSemiring R] :
-- imply
  PrimeSpectrum.vanishingIdeal (R := R) '' {s | IsClosed s ∧ IsIrreducible s} = {P | P.IsPrime} :=
-- proof
  PrimeSpectrum.vanishingIdeal_isClosed_isIrreducible

/--
[specIrreducible_iff_isPrime_nilradical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma specIrreducible_iff_isPrime_nilradical
  [CommSemiring R] :
-- imply
  IrreducibleSpace (PrimeSpectrum R) ↔ (nilradical R).IsPrime :=
-- proof
  PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical
end IrreducibilityAndPrimes
section IrreducibleDomain
variable {R : Type*} [CommRing R]

/--
[specIrreducible_iff_isDomain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma specIrreducible_iff_isDomain
  [CommRing R]
  [IsReduced R] :
-- imply
  IrreducibleSpace (PrimeSpectrum R) ↔ IsDomain R := by
-- proof
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical, nilradical_eq_zero R]
  exact ⟨fun _ => IsDomain.of_bot_isPrime R, fun _ => Ideal.isPrime_bot⟩

/--
[specIrreducible_of_isDomain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma specIrreducible_of_isDomain
  [CommRing R]
  [IsDomain R] :
-- imply
  IrreducibleSpace (PrimeSpectrum R) :=
-- proof
  PrimeSpectrum.irreducibleSpace
end IrreducibleDomain
section RadicalDecomposition
variable {R : Type*} [CommSemiring R]

/--
[radical_eq_sInf_primes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma radical_eq_sInf_primes
  [CommSemiring R]
  {I : Ideal R} :
-- imply
  I.radical = sInf {J : Ideal R | I ≤ J ∧ J.IsPrime} :=
-- proof
  Ideal.radical_eq_sInf I

/--
[radical_eq_sInf_minimalPrimes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma radical_eq_sInf_minimalPrimes
  [CommSemiring R]
  {I : Ideal R} :
-- imply
  I.radical = sInf I.minimalPrimes :=
-- proof
  (Ideal.sInf_minimalPrimes).symm

/--
[finite_minimalPrimes_of_noetherian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma finite_minimalPrimes_of_noetherian
  [CommSemiring R]
  [IsNoetherianRing R]
  {I : Ideal R} :
-- imply
  I.minimalPrimes.Finite :=
-- proof
  Ideal.finite_minimalPrimes_of_isNoetherianRing R I

/--
[radical_eq_finite_iInf_primes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma radical_eq_finite_iInf_primes
  [CommSemiring R]
  [IsNoetherianRing R]
  {I : Ideal R} :
-- imply
  ∃ (S : Finset (Ideal R)), (∀ J ∈ S, J.IsPrime) ∧ I.radical = S.inf id := by
-- proof
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing R I
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro J hJ
    rwa [Set.Finite.mem_toFinset] at hJ
  · rw [← Ideal.sInf_minimalPrimes]
    conv_lhs => rw [show I.minimalPrimes = ↑hfin.toFinset from (hfin.coe_toFinset).symm]
    exact (Finset.inf_id_eq_sInf hfin.toFinset).symm

/--
[isRadical_eq_finite_iInf_primes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma isRadical_eq_finite_iInf_primes
  [CommSemiring R]
  [IsNoetherianRing R]
  {I : Ideal R}
-- given
  (hI : I.IsRadical) :
-- imply
  ∃ (S : Finset (Ideal R)), (∀ J ∈ S, J.IsPrime) ∧ I = S.inf id := by
-- proof
  obtain ⟨S, hS, heq⟩ := radical_eq_finite_iInf_primes I
  exact ⟨S, hS, hI.radical ▸ heq⟩

/--
[finite_minimalPrimes_of_noetherian_ring](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean)
-/
@[path]
lemma finite_minimalPrimes_of_noetherian_ring
  [CommSemiring R]
  [IsNoetherianRing R] :
-- imply
  (minimalPrimes R).Finite :=
-- proof
  minimalPrimes.finite_of_isNoetherianRing R
end RadicalDecomposition


-- created on 2026-10-23
