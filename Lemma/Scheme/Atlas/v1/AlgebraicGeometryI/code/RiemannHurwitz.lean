import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitz
open Ideal Module
open Algebra


/--
[fundamental_identity_ramification](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma fundamental_identity_ramification
  [CommRing R]
  [IsDedekindDomain R]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  ∑ P ∈ primesOverFinset p S, p.ramificationIdx P * p.inertiaDeg P = finrank K L :=
-- proof
  sum_ramification_inertia S K L hp0

/--
[fundamental_identity_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma fundamental_identity_local
  [CommRing R]
  [IsDedekindDomain R]
  [IsLocalRing S]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  p.ramificationIdx (IsLocalRing.maximalIdeal S) * p.inertiaDeg (IsLocalRing.maximalIdeal S) = finrank K L :=
-- proof
  ramificationIdx_mul_inertiaDeg_of_isLocalRing S K L hp0
section Unramified
variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

/--
[ramificationIdx_eq_one_of_isUnramifiedAt'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma ramificationIdx_eq_one_of_isUnramifiedAt'
  [CommRing R]
  [CommRing S]
  [Algebra R S]
  {p : Ideal R}
  {P : Ideal S}
  [P.IsPrime]
  [hlo : P.LiesOver p]
  [IsDomain S]
  [IsNoetherianRing S]
  [Algebra.EssFiniteType R S]
-- given
  (h : IsUnramifiedAt' p P)
  (hP : P ≠ ⊥) :
-- imply
  p.ramificationIdx P = 1 := by
-- proof
  have hpq : p = P.under R := hlo.over
  subst hpq
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := R) hP

/--
[isUnramifiedAt'_iff_ramificationIdx_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma isUnramifiedAt'_iff_ramificationIdx_eq_one
  [CommRing R]
  [CommRing S]
  [Algebra R S]
  {p : Ideal R}
  {P : Ideal S}
  [P.IsPrime]
  [hlo : P.LiesOver p]
  [IsDedekindDomain S]
  [Algebra.EssFiniteType R S]
  [IsDomain R]
  [Module.Finite ℤ R]
  [CharZero R]
  [Algebra.IsIntegral R S]
-- given
  (hP : P ≠ ⊥) :
-- imply
  IsUnramifiedAt' p P ↔ p.ramificationIdx P = 1 := by
-- proof
  have hpq : p = P.under R := hlo.over
  subst hpq
  exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain hP
end Unramified
section Discriminant
open Algebra

/--
[discriminant_ne_zero_of_separable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma discriminant_ne_zero_of_separable
  [DecidableEq ι]
  [Fintype ι]
  {K : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [Module.Finite K L]
  [Algebra.IsSeparable K L]
  {b : Basis ι K L} :
-- imply
  discr K b ≠ 0 :=
-- proof
  discr_not_zero_of_basis K b

/--
[discriminant_isUnit_of_separable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma discriminant_isUnit_of_separable
  [DecidableEq ι]
  [Fintype ι]
  {K : Type*}
  [Field K]
  [Field L]
  [Algebra K L]
  [Module.Finite K L]
  [Algebra.IsSeparable K L]
  {b : Basis ι K L} :
-- imply
  IsUnit (discr K b) :=
-- proof
  discr_isUnit_of_basis K b
end Discriminant
section RamificationBounds
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
  (K L : Type*) [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L]
  [Algebra K L] [Algebra R L]
  [IsScalarTower R S L] [IsScalarTower R K L]
  [Module.Finite R S]

/--
[card_primes_over_le_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma card_primes_over_le_finrank
  [CommRing R]
  [IsDedekindDomain R]
  [NoZeroSMulDivisors R S]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  Finset.card (primesOverFinset p S) ≤ finrank K L :=
-- proof
  card_primesOverFinset_le_finrank S K L hp0

/--
[sum_ramificationIdx_le_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma sum_ramificationIdx_le_finrank
  [CommRing R]
  [IsDedekindDomain R]
  [NoZeroSMulDivisors R S]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  ∑ P ∈ primesOverFinset p S, p.ramificationIdx P ≤ finrank K L := by
-- proof
  rw [← sum_ramification_inertia S K L hp0]
  apply Finset.sum_le_sum
  intro P hP
  have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
  have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
  exact Nat.le_mul_of_pos_right _ (inertiaDeg_pos p P)

/--
[ramificationIdx_le_finrank'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma ramificationIdx_le_finrank'
  [CommRing R]
  [IsDedekindDomain R]
  [NoZeroSMulDivisors R S]
  {p : Ideal R}
  [p.IsMaximal]
  {P : Ideal S}
  [P.IsPrime]
  [P.LiesOver p] :
-- imply
  p.ramificationIdx P ≤ finrank K L :=
-- proof
  ramificationIdx_le_finrank S K L P

/--
[inertiaDeg_le_finrank'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma inertiaDeg_le_finrank'
  [CommRing R]
  [IsDedekindDomain R]
  [NoZeroSMulDivisors R S]
  {p : Ideal R}
  [p.IsMaximal]
  {P : Ideal S}
  [P.IsPrime]
  [P.LiesOver p]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  inertiaDeg p P ≤ finrank K L :=
-- proof
  inertiaDeg_le_finrank S K L P hp0
end RamificationBounds
section Chevalley

/--
[dedekind_lying_over](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma dedekind_lying_over
  {R S : Type*}
  [CommRing R]
  [IsDedekindDomain R]
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
  [Module.Finite R S]
  [FaithfulSMul R S]
  {p : Ideal R}
  [hp : p.IsPrime]
-- given
  (_hp0 : p ≠ ⊥) :
-- imply
  ∃ (P : Ideal S), P.IsPrime ∧ P.LiesOver p := by
-- proof
  have hSurj := finite_morphism_spec_surjective R S
  obtain ⟨Q, hQ⟩ := hSurj ⟨p, hp⟩
  refine ⟨Q.asIdeal, Q.isPrime, ⟨?_⟩⟩
  have : PrimeSpectrum.comap (algebraMap R S) Q = ⟨p, hp⟩ := hQ
  simp [PrimeSpectrum.comap] at this
  exact this.symm

/--
[dedekind_contraction_is_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma dedekind_contraction_is_prime
  {R S : Type*}
  [CommRing R]
  [IsDedekindDomain R]
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
  {P : Ideal S}
  [hP : P.IsPrime] :
-- imply
  (P.comap (algebraMap R S)).IsPrime :=
-- proof
  Ideal.IsPrime.comap (algebraMap R S)

/--
[primes_over_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma primes_over_finite
  [CommRing R]
  [IsDedekindDomain R]
  [NoZeroSMulDivisors R S]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  Set.Finite (primesOver p S) := by
-- proof
  rw [← coe_primesOverFinset hp0 S]
  exact (primesOverFinset p S).finite_toSet
section RiemannHurwitzFormula

/--
[totalRamificationAt_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma totalRamificationAt_nonneg
  [CommRing R]
  [IsDedekindDomain R]
  {S : Type*}
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
  [NoZeroSMulDivisors R S]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  0 ≤ totalRamificationAt S p hp0 := by
-- proof
  unfold totalRamificationAt
  apply Finset.sum_nonneg
  intro P hP
  have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
  have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
  have := IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
  omega

/--
[totalRamificationAt_le_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma totalRamificationAt_le_finrank
  [CommRing R]
  [IsDedekindDomain R]
  {S : Type*}
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra R K]
  [IsFractionRing R K]
  [Algebra S L]
  [IsFractionRing S L]
  [Algebra K L]
  [Algebra R L]
  [IsScalarTower R S L]
  [IsScalarTower R K L]
  [Module.Finite R S]
  [NoZeroSMulDivisors R S]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  totalRamificationAt S p hp0 ≤ finrank K L := by
-- proof
  unfold totalRamificationAt
  have hfund := sum_ramification_inertia S K L hp0
  calc ∑ P ∈ primesOverFinset p S,
    ((p.ramificationIdx P : ℤ) - 1)
    ≤ ∑ P ∈ primesOverFinset p S,
      (p.ramificationIdx P : ℤ) := by
        apply Finset.sum_le_sum; intro P _; omega
    _ ≤ ∑ P ∈ primesOverFinset p S,
      ((p.ramificationIdx P * p.inertiaDeg P : ℕ) : ℤ) := by
      apply Finset.sum_le_sum
      intro P hP
      have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
      have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
      exact_mod_cast Nat.le_mul_of_pos_right _ (inertiaDeg_pos p P)
    _ = (finrank K L : ℤ) := by exact_mod_cast hfund

/--
[totalRamificationAt_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma totalRamificationAt_eq_zero_iff
  [CommRing R]
  [IsDedekindDomain R]
  {S : Type*}
  [CommRing S]
  [IsDedekindDomain S]
  [Algebra R S]
  [NoZeroSMulDivisors R S]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  totalRamificationAt S p hp0 = 0 ↔ ∀ P ∈ primesOverFinset p S, p.ramificationIdx P = 1 := by
-- proof
  unfold totalRamificationAt
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h P hP
      have := h P hP
      have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
      have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
      have := IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
      omega
    · intro h P hP
      simp [h P hP]
  · intro P hP
    have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
    have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
    have := IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
    omega

/--
[riemann_hurwitz_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma riemann_hurwitz_formula
  {n g_X g_Y : ℤ}
  {deg_R deg_KX deg_KY deg_pullback : ℤ}
-- given
  (h_deg_KX : deg_KX = 2 * g_X - 2)
  (h_deg_KY : deg_KY = 2 * g_Y - 2)
  (h_pullback : deg_pullback = n * deg_KY)
  (h_canonical : deg_KX = deg_pullback + deg_R) :
-- imply
  2 * g_X - 2 = n * (2 * g_Y - 2) + deg_R := by
-- proof
  subst h_deg_KX; subst h_deg_KY; subst h_pullback; linarith

/--
[riemann_hurwitz_ramification_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma riemann_hurwitz_ramification_eq
  {n g_X g_Y R : ℤ}
-- given
  (hRH : 2 * g_X - 2 = n * (2 * g_Y - 2) + R) :
-- imply
  R = 2 * g_X - 2 - n * (2 * g_Y - 2) := by
-- proof
linarith

/--
[riemann_hurwitz_genus_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma riemann_hurwitz_genus_bound
  {n g_X g_Y R : ℤ}
-- given
  (hR : 0 ≤ R)
  (hRH : 2 * g_X - 2 = n * (2 * g_Y - 2) + R) :
-- imply
  g_X ≥ n * g_Y - n + 1 := by
-- proof
linarith

/--
[riemann_hurwitz_with_arithmeticGenus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma riemann_hurwitz_with_arithmeticGenus
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  [Algebra k A]
  [Module.Finite k A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDedekindDomain B]
  [Algebra k B]
  [Module.Finite k B]
  {n : ℤ}
  {total_ramification : ℤ}
-- given
  (h_formula : (2 : ℤ) * RiemannRochGeneral.arithmeticGenus k B - 2 = n * (2 * RiemannRochGeneral.arithmeticGenus k A - 2) + total_ramification) :
-- imply
  total_ramification = 2 * (RiemannRochGeneral.arithmeticGenus k B : ℤ) - 2 - n * (2 * RiemannRochGeneral.arithmeticGenus k A - 2) := by
-- proof
  linarith

/--
[riemann_hurwitz_hyperelliptic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma riemann_hurwitz_hyperelliptic
  {g : ℤ} :
-- imply
  2 * g - 2 = 2 * (2 * 0 - 2) + (2 * g + 2) := by
-- proof
ring

/--
[riemann_hurwitz_hyperelliptic_ramification](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean)
-/
@[path]
lemma riemann_hurwitz_hyperelliptic_ramification
  {g R : ℤ}
-- given
  (hRH : 2 * g - 2 = 2 * (2 * 0 - 2) + R) :
-- imply
  R = 2 * g + 2 := by
-- proof
linarith


-- created on 2026-10-23
