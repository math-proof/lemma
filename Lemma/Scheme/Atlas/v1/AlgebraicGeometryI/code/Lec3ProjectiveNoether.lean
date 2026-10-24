import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec3ProjectiveNoether
open PrimeSpectrum TopologicalSpace AlgebraicGeometry CategoryTheory
open CategoryTheory


/--
[thm3_1_affine_iff_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ProjectiveNoether.lean)
-/
@[path]
lemma thm3_1_affine_iff_spec
  {k : Type v}
  [Field k]
  [IsAlgClosed k] :
-- imply
  (∀ (X : Scheme.{v}) (f : X ⟶ Spec (CommRingCat.of k)) [Definition3_AlgebraicVariety k X f] [IsAffine X], IsIso X.toSpecΓ ∧ _root_.IsReduced Γ(X, ⊤) ∧ RingHom.FiniteType (f.appTop.hom)) ∧ (∀ (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] [IsReduced A], Definition3_AlgebraicVariety k (Spec (CommRingCat.of A)) (Spec.map (CommRingCat.ofHom (algebraMap k A)))) :=
-- proof
  thm31_affine_variety_characterization (k := k)

/--
[thm3_2_noether_normalization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ProjectiveNoether.lean)
-/
@[path]
lemma thm3_2_noether_normalization
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [Nontrivial A]
  [Algebra k A]
  [Algebra.FiniteType k A] :
-- imply
  ∃ (d : ℕ) (g : MvPolynomial (Fin d) k →ₐ[k] A), Function.Injective g ∧ g.Finite :=
-- proof
  noether_normalization_finite k A

/--
[lemma3_linear_change_monic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ProjectiveNoether.lean)
-/
@[path]
lemma lemma3_linear_change_monic
  [Field k]
  [Infinite k]
  {n : ℕ}
  {P : MvPolynomial (Fin (n + 1)) k}
-- given
  (hP : 0 < P.totalDegree) :
-- imply
  ∃ (φ : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k), IsUnit (MvPolynomial.finSuccEquiv k n (φ P)).leadingCoeff :=
-- proof
  MvPolynomial.exists_algEquiv_monic P hP

/--
[lemma3_nonzero_polynomial_takes_nonzero_values](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ProjectiveNoether.lean)
-/
@[path]
lemma lemma3_nonzero_polynomial_takes_nonzero_values
  [Field k]
  [Infinite k]
  [Fintype σ]
  {f : MvPolynomial σ k}
-- given
  (hf : f ≠ 0) :
-- imply
  ∃ v : σ → k, MvPolynomial.eval v f ≠ 0 :=
-- proof
  MvPolynomial.exists_eval_ne_zero hf

/--
[prop2_hilbert_basis_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ProjectiveNoether.lean)
-/
@[path]
lemma prop2_hilbert_basis_theorem
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  IsNoetherianRing (MvPolynomial (Fin n) k) :=
-- proof
  inferInstance

/--
[lemma4_nakayama](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ProjectiveNoether.lean)
-/
@[path]
lemma lemma4_nakayama
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  {I : Ideal R}
-- given
  (hIM : I • (⊤ : Submodule R M) = ⊤) :
-- imply
  ∃ a : R, a - 1 ∈ I ∧ ∀ m : M, a • m = 0 :=
-- proof
  nakayama_determinant_form I hIM

/--
[thm3_3_essential_nullstellensatz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ProjectiveNoether.lean)
-/
@[path]
lemma thm3_3_essential_nullstellensatz
  {k : Type*}
  [Field k]
  {A : Type*}
  [Field A]
  [Algebra k A]
  [Algebra.FiniteType k A] :
-- imply
  Algebra.IsAlgebraic k A :=
-- proof
  essential_nullstellensatz k A

/--
[def7_irreducible_space_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ProjectiveNoether.lean)
-/
@[path]
lemma def7_irreducible_space_iff
  {X : Type*}
  [TopologicalSpace X] :
-- imply
  IrreducibleSpace X ↔ IsIrreducible (Set.univ : Set X) :=
-- proof
  irreducibleSpace_def X

/--
[def7_irreducible_not_union_proper_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ProjectiveNoether.lean)
-/
@[path]
lemma def7_irreducible_not_union_proper_closed
  {X : Type*}
  [TopologicalSpace X]
  [IrreducibleSpace X]
  {s t : Set X}
-- given
  (hs : IsClosed s)
  (ht : IsClosed t)
  (hst : s ∪ t = Set.univ) :
-- imply
  s = Set.univ ∨ t = Set.univ := by
-- proof
  have hirr := (IrreducibleSpace.isIrreducible_univ X).isPreirreducible
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hirr
  have hsub : Set.univ ⊆ s ∪ t := hst ▸ le_refl _
  obtain h | h := hirr s t hs ht hsub
  · left; exact Set.univ_subset_iff.mp h
  · right; exact Set.univ_subset_iff.mp h

/--
[prop3_spec_irreducible_iff_domain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ProjectiveNoether.lean)
-/
@[path]
lemma prop3_spec_irreducible_iff_domain
  {A : Type*}
  [CommRing A]
  [IsReduced A] :
-- imply
  IrreducibleSpace (PrimeSpectrum A) ↔ IsDomain A := by
-- proof
  rw [PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical]
  have hnil : nilradical A = ⊥ := nilradical_eq_zero A
  rw [hnil]
  exact ⟨fun _ => IsDomain.of_bot_isPrime A, fun _ => Ideal.isPrime_bot⟩

/--
[def8_component_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ProjectiveNoether.lean)
-/
@[path]
lemma def8_component_characterization
  {X : Type*}
  [TopologicalSpace X]
  {s : Set X} :
-- imply
  s ∈ irreducibleComponents X ↔ IsIrreducible s ∧ ∀ t : Set X, IsIrreducible t → s ⊆ t → t ⊆ s := by
-- proof
  simp only [irreducibleComponents, Set.mem_setOf_eq, Maximal]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun t ht hst => h2 ht hst⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun {t} ht hst => h2 t ht hst⟩

/--
[def8_component_is_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ProjectiveNoether.lean)
-/
@[path]
lemma def8_component_is_closed
  {X : Type*}
  [TopologicalSpace X]
  {s : Set X}
-- given
  (hs : s ∈ irreducibleComponents X) :
-- imply
  IsClosed s :=
-- proof
  isClosed_of_mem_irreducibleComponents s hs

/--
[prop4_noetherian_finite_union_components](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ProjectiveNoether.lean)
-/
@[path]
lemma prop4_noetherian_finite_union_components
  {X : Type*}
  [TopologicalSpace X]
  [NoetherianSpace X] :
-- imply
  Set.Finite (irreducibleComponents X) ∧ ⋃₀ irreducibleComponents X = Set.univ := by
-- proof
  refine ⟨NoetherianSpace.finite_irreducibleComponents, ?_⟩
  ext x
  simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
  exact ⟨irreducibleComponent x,
    irreducibleComponent_mem_irreducibleComponents x,
    mem_irreducibleComponent⟩

/--
[cor5_irreducible_closed_iff_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ProjectiveNoether.lean)
-/
@[path]
lemma cor5_irreducible_closed_iff_prime
  {A : Type*}
  [CommRing A]
  {I : Ideal A}
-- given
  (hI : I.IsRadical) :
-- imply
  IsIrreducible (PrimeSpectrum.zeroLocus (I : Set A)) ↔ I.IsPrime :=
-- proof
  PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical I hI

/--
[cor5_closed_irreducible_eq_primes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ProjectiveNoether.lean)
-/
@[path]
lemma cor5_closed_irreducible_eq_primes
  {A : Type*}
  [CommRing A] :
-- imply
  PrimeSpectrum.vanishingIdeal '' {s : Set (PrimeSpectrum A) | IsClosed s ∧ IsIrreducible s} = {P : Ideal A | P.IsPrime} :=
-- proof
  PrimeSpectrum.vanishingIdeal_isClosed_isIrreducible

/--
[cor5_components_eq_minimal_primes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ProjectiveNoether.lean)
-/
@[path]
lemma cor5_components_eq_minimal_primes
  {A : Type*}
  [CommRing A]
  [IsNoetherianRing A] :
-- imply
  PrimeSpectrum.vanishingIdeal '' irreducibleComponents (PrimeSpectrum A) = minimalPrimes A :=
-- proof
  PrimeSpectrum.vanishingIdeal_irreducibleComponents A

/--
[cor6_zero_eq_inf_minimal_primes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec3ProjectiveNoether.lean)
-/
@[path]
lemma cor6_zero_eq_inf_minimal_primes
  {A : Type*}
  [CommRing A]
  [IsReduced A] :
-- imply
  sInf (Ideal.minimalPrimes (⊥ : Ideal A)) = (⊥ : Ideal A) := by
-- proof
  rw [Ideal.sInf_minimalPrimes]
  change nilradical A = ⊥
  exact nilradical_eq_zero A


-- created on 2026-10-23
