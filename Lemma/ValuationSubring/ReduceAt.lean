import Mathlib
import Lemma.WeierstrassCurve.ReductionMap
import Instance.ValuationSubring_ReduceAt

set_option autoImplicit false

open IsLocalRing Polynomial

namespace ValuationSubring

section ResidueAlgClosed

variable {L : Type*} [Field L] (A : ValuationSubring L)

variable {A}

theorem pow_residueChar_bijective [IsAlgClosed L] {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) :
    Function.Bijective (fun x : ResidueField A => x ^ q) := by
  haveI : CharP (ResidueField A) q := charP_residueField_of_liesOverPrime_def hq hA
  haveI : Fact q.Prime := ⟨hq⟩
  constructor
  ·
    intro x y hxy
    have hxy' : x ^ q = y ^ q := hxy
    have hsub : (x - y) ^ q = 0 := by
      rw [sub_pow_char, hxy', sub_self]
    have := pow_eq_zero_iff hq.ne_zero |>.mp hsub
    exact sub_eq_zero.mp this
  ·
    intro x
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq x hq.pos
    exact ⟨y, hy⟩

end ResidueAlgClosed

variable {L : Type*} [Field L]

section IntegerUnits

variable {A : ValuationSubring L} {ℓ : ℕ}

theorem intCast_isUnit_of_not_dvd (hℓ : ℓ.Prime) (hA : A.LiesOverPrime ℓ) {n : ℤ}
    (hn : ¬(ℓ : ℤ) ∣ n) : IsUnit ((n : ℤ) : A) := by
  by_contra hunit

  have hnmem : ((n : ℤ) : A) ∈ maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal]
    exact hunit

  have hℓmem : ((ℓ : ℕ) : A) ∈ maximalIdeal A := natCast_mem_maximalIdeal_of_liesOverPrime hA

  obtain ⟨u, v, huv⟩ := (Nat.prime_iff_prime_int.mp hℓ).coprime_iff_not_dvd.mpr hn

  have h1 : (1 : A) ∈ maximalIdeal A := by
    have h := congrArg (fun z : ℤ => ((z : ℤ) : A)) huv
    simp only [Int.cast_add, Int.cast_mul, Int.cast_one, Int.cast_natCast] at h
    rw [← h]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hℓmem) (Ideal.mul_mem_left _ _ hnmem)
  exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem residue_intCast_ne_zero (hℓ : ℓ.Prime) (hA : A.LiesOverPrime ℓ) {n : ℤ}
    (hn : ¬(ℓ : ℤ) ∣ n) : residue A ((n : ℤ) : A) ≠ 0 :=
  (residue_ne_zero_iff_isUnit _).mpr (intCast_isUnit_of_not_dvd hℓ hA hn)

theorem gate_not_liesOverPrime_of_ne (hℓ : ℓ.Prime) (hA : A.LiesOverPrime ℓ) {q : ℕ}
    (hq : q.Prime) (hne : q ≠ ℓ) : ¬A.LiesOverPrime q := by
  intro hq'
  have hqmem : ((q : ℕ) : A) ∈ maximalIdeal A := natCast_mem_maximalIdeal_of_liesOverPrime hq'
  have hqdvd : ¬(ℓ : ℤ) ∣ (q : ℤ) := by
    intro h
    rcases (Nat.prime_dvd_prime_iff_eq hℓ hq).mp (Int.natCast_dvd_natCast.mp h) with rfl
    exact hne rfl
  have := intCast_isUnit_of_not_dvd hℓ hA hqdvd
  rw [IsLocalRing.mem_maximalIdeal] at hqmem
  exact hqmem (by exact_mod_cast this)

end IntegerUnits

section Algebraicity

variable (A : ValuationSubring L) {ℓ : ℕ}

theorem isAlgebraic_residue [CharZero L] [Algebra ℚ L]
    [Algebra.IsAlgebraic ℚ L] (hℓ : ℓ.Prime)
    [Algebra (ZMod ℓ) (ResidueField A)] (a : A) :
    IsAlgebraic (ZMod ℓ) (residue A a) := by

  obtain ⟨p, hp0, hpa⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (a : L)

  set P₀ : ℤ[X] := IsLocalization.integerNormalization (nonZeroDivisors ℤ) p with hP₀def
  have hP₀a : aeval (a : L) P₀ = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) p hpa
  have hP₀0 : P₀ ≠ 0 := fun h =>
    hp0 ((IsLocalization.integerNormalization_eq_zero_iff le_rfl p).mp h)

  set P : ℤ[X] := P₀.primPart with hPdef
  have hPa : aeval (a : L) P = 0 := aeval_primPart_eq_zero hP₀0 hP₀a
  have hPprim : P.IsPrimitive := P₀.isPrimitive_primPart
  have hP0 : P ≠ 0 := P₀.primPart_ne_zero

  have hcoeff : ∃ i, ¬(ℓ : ℤ) ∣ P.coeff i := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hu : IsUnit ((ℓ : ℤ)) := hPprim _ ((C_dvd_iff_dvd_coeff _ _).mpr h)
    rw [Int.isUnit_iff] at hu
    have h2 := hℓ.two_le
    omega

  have hPaA : aeval a P = 0 := by
    have hmap : algebraMap A L (aeval a P) = 0 := by
      rw [← Polynomial.aeval_algebraMap_apply]
      exact hPa
    exact (map_eq_zero_iff _ Subtype.coe_injective).mp hmap

  have hPres : aeval (residue A a) P = 0 := by
    have hcomm : aeval (residue A a) P = (residue A) (aeval a P) :=
      Polynomial.aeval_algHom_apply (RingHom.toIntAlgHom (residue A)) a P
    rw [hcomm, hPaA, map_zero]

  refine ⟨P.map (algebraMap ℤ (ZMod ℓ)), ?_, ?_⟩
  ·
    obtain ⟨i, hi⟩ := hcoeff
    intro h0
    apply hi
    have hzero : (P.map (algebraMap ℤ (ZMod ℓ))).coeff i = 0 := by rw [h0]; simp
    rw [coeff_map] at hzero
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
  ·
    rw [aeval_def, eval₂_map,
      show (algebraMap (ZMod ℓ) (ResidueField A)).comp (algebraMap ℤ (ZMod ℓ))
          = algebraMap ℤ (ResidueField A) from RingHom.ext_int _ _,
      ← aeval_def]
    exact hPres

theorem gate_isAlgebraic_int_vacuous_of_charP {R : Type*} [CommRing R] [Nontrivial R]
    {ℓ : ℕ} (hℓ : ℓ.Prime) [CharP R ℓ] (x : R) : IsAlgebraic ℤ x := by
  refine ⟨C (ℓ : ℤ) * X, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun q : ℤ[X] => q.coeff 1) h
    simp only [coeff_C_mul, coeff_X_one, mul_one, coeff_zero] at hc
    have h2 := hℓ.two_le
    omega
  · simp

end Algebraicity

section Identification

variable (A : ValuationSubring L) {ℓ : ℕ}

theorem isAlgClosure_residueField [IsAlgClosed L] [CharZero L] [Algebra ℚ L]
    [Algebra.IsAlgebraic ℚ L] [Fact ℓ.Prime]
    [Algebra (ZMod ℓ) (ResidueField A)] :
    IsAlgClosure (ZMod ℓ) (ResidueField A) := by
  refine ⟨inferInstance, ⟨fun x => ?_⟩⟩
  obtain ⟨a, rfl⟩ := residue_surjective (R := A) x
  exact isAlgebraic_residue A Fact.out a

noncomputable def residueFieldEquivAlgebraicClosure [IsAlgClosed L] [CharZero L] [Algebra ℚ L]
    [Algebra.IsAlgebraic ℚ L] [Fact ℓ.Prime] (hA : A.LiesOverPrime ℓ) :
    ResidueField A ≃+* AlgebraicClosure (ZMod ℓ) := by
  haveI hchar : CharP (ResidueField A) ℓ := charP_residueField_of_liesOverPrime_def Fact.out hA
  letI halg : Algebra (ZMod ℓ) (ResidueField A) := ZMod.algebra (ResidueField A) ℓ

  haveI htf : Module.IsTorsionFree (ZMod ℓ) (ResidueField A) := by
    refine Module.IsTorsionFree.of_smul_eq_zero (fun r m h => ?_)
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact Or.inl ((map_eq_zero_iff _ (algebraMap (ZMod ℓ) (ResidueField A)).injective).mp h')
    · exact Or.inr h'
  haveI hcl : IsAlgClosure (ZMod ℓ) (ResidueField A) := isAlgClosure_residueField A
  exact (IsAlgClosure.equiv (ZMod ℓ) (ResidueField A) (AlgebraicClosure (ZMod ℓ))).toRingEquiv

end Identification

section ReduceAt

variable {ℓ : ℕ} [Fact ℓ.Prime]
variable (A : ValuationSubring L) [IsAlgClosed L] [CharZero L] [Algebra ℚ L]
  [Algebra.IsAlgebraic ℚ L]
variable (hA : A.LiesOverPrime ℓ)

open Classical in

noncomputable def reduceAt (a : L) : AlgebraicClosure (ZMod ℓ) :=
  if h : a ∈ A then residueFieldEquivAlgebraicClosure A hA (residue A ⟨a, h⟩) else 0

variable {A hA}

theorem reduceAt_of_mem {a : L} (h : a ∈ A) :
    reduceAt A hA a = residueFieldEquivAlgebraicClosure A hA (residue A ⟨a, h⟩) :=
  dif_pos h

theorem reduceAt_of_notMem {a : L} (h : a ∉ A) : reduceAt A hA a = 0 :=
  dif_neg h

@[simp]
theorem reduceAt_coe (a : A) :
    reduceAt A hA (a : L) = residueFieldEquivAlgebraicClosure A hA (residue A a) :=
  reduceAt_of_mem a.2

@[simp]
theorem reduceAt_zero : reduceAt A hA (0 : L) = 0 := by
  have h := reduceAt_coe (A := A) (hA := hA) (0 : A)
  simpa using h

@[simp]
theorem reduceAt_one : reduceAt A hA (1 : L) = 1 := by
  have h := reduceAt_coe (A := A) (hA := hA) (1 : A)
  simpa using h

theorem reduceAt_add {a b : L} (ha : a ∈ A) (hb : b ∈ A) :
    reduceAt A hA (a + b) = reduceAt A hA a + reduceAt A hA b := by
  rw [reduceAt_of_mem ha, reduceAt_of_mem hb, reduceAt_of_mem (A.add_mem _ _ ha hb),
    show (⟨a + b, A.add_mem _ _ ha hb⟩ : A) = ⟨a, ha⟩ + ⟨b, hb⟩ from rfl, map_add, map_add]

theorem reduceAt_mul {a b : L} (ha : a ∈ A) (hb : b ∈ A) :
    reduceAt A hA (a * b) = reduceAt A hA a * reduceAt A hA b := by
  rw [reduceAt_of_mem ha, reduceAt_of_mem hb, reduceAt_of_mem (A.mul_mem _ _ ha hb),
    show (⟨a * b, A.mul_mem _ _ ha hb⟩ : A) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, map_mul, map_mul]

theorem reduceAt_surjective : Function.Surjective (reduceAt A hA) := by
  intro y
  obtain ⟨a, ha⟩ :=
    residue_surjective (R := A) ((residueFieldEquivAlgebraicClosure A hA).symm y)
  exact ⟨(a : L), by rw [reduceAt_coe, ha, RingEquiv.apply_symm_apply]⟩

theorem reduceAt_eq_zero_iff_of_mem {a : L} (h : a ∈ A) :
    reduceAt A hA a = 0 ↔ (⟨a, h⟩ : A) ∈ maximalIdeal A := by
  rw [reduceAt_of_mem h,
    map_eq_zero_iff _ (residueFieldEquivAlgebraicClosure A hA).injective]
  exact residue_eq_zero_iff _

@[simp]
theorem reduceAt_intCast (n : ℤ) :
    reduceAt A hA ((n : ℤ) : L) = ((n : ℤ) : AlgebraicClosure (ZMod ℓ)) := by
  have hmem : ((n : ℤ) : L) = (((n : ℤ) : A) : L) := by norm_cast
  rw [hmem, reduceAt_coe, map_intCast (residue A) n]
  exact map_intCast (residueFieldEquivAlgebraicClosure A hA) n

@[simp]
theorem reduceAt_natCast (n : ℕ) :
    reduceAt A hA ((n : ℕ) : L) = ((n : ℕ) : AlgebraicClosure (ZMod ℓ)) := by
  have h := reduceAt_intCast (A := A) (hA := hA) (n : ℤ)
  push_cast at h
  exact h

theorem reduceAt_residueChar : reduceAt A hA ((ℓ : ℕ) : L) = 0 := by
  rw [reduceAt_natCast]
  exact CharP.cast_eq_zero (AlgebraicClosure (ZMod ℓ)) ℓ

theorem reduceAt_intCast_ne_zero {n : ℤ} (hn : ¬(ℓ : ℤ) ∣ n) :
    reduceAt A hA ((n : ℤ) : L) ≠ 0 := by
  rw [reduceAt_intCast]
  intro h
  apply hn
  rw [show ((n : ℤ) : AlgebraicClosure (ZMod ℓ))
      = algebraMap (ZMod ℓ) (AlgebraicClosure (ZMod ℓ)) ((n : ℤ) : ZMod ℓ) from
    (map_intCast _ n).symm] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd n ℓ).mp
    ((map_eq_zero_iff _ (algebraMap (ZMod ℓ) (AlgebraicClosure (ZMod ℓ))).injective).mp h)

end ReduceAt

end ValuationSubring
