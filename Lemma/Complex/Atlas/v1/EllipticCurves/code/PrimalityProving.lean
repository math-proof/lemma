import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.PrimalityProving
open Classical
open scoped Nat
open WeierstrassCurve


/--
[fermat_little_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean)
-/
@[path]
lemma fermat_little_theorem
  {p : ℕ}
  [Fact p.Prime]
  {a : ZMod p} :
-- imply
  a ^ p = a :=
-- proof
  ZMod.pow_card a

/--
[totient_eq_sub_one_iff_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean)
-/
@[path]
lemma totient_eq_sub_one_iff_prime
  {N : ℕ}
-- given
  (hN : 2 ≤ N) :
-- imply
  N.totient = N - 1 ↔ N.Prime :=
-- proof
  Nat.totient_eq_iff_prime (by omega)

/--
[millerRabin_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean)
-/
@[path]
lemma millerRabin_decomp
  {N : ℕ} :
-- imply
  N - 1 = 2 ^ millerRabinS N * millerRabinD N := by
-- proof
  simp only [millerRabinD, millerRabinS]
  have h := Nat.div_mul_cancel (pow_multiplicity_dvd 2 (N - 1))
  linarith

/--
[sq_chain_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean)
-/
@[path]
lemma sq_chain_dichotomy
  [CommRing R]
  [IsDomain R]
  {x : R}
  {n : ℕ}
-- given
  (h : x ^ (2 ^ n) = 1) :
-- imply
  x = 1 ∨ ∃ i : ℕ, i < n ∧ x ^ (2 ^ i) = -1 := by
-- proof
  induction n with
  | zero => simp [pow_zero, pow_one] at h; exact Or.inl h
  | succ n ih =>
    have h2 : (x ^ (2 ^ n)) ^ 2 = 1 := by
      rw [← pow_mul, ← pow_succ]; exact h
    rw [sq_eq_one_iff] at h2
    obtain h_one | h_neg := h2
    · rcases ih h_one with h1 | ⟨i, hi, hx⟩
      · exact Or.inl h1
      · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hx⟩
    · exact Or.inr ⟨n, Nat.lt_succ_iff.mpr le_rfl, h_neg⟩

/--
[lemma_11_6](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean)
-/
@[path]
lemma lemma_11_6
  {p : ℕ}
  {a : ZMod p}
-- given
  (hp : p.Prime)
  (ha : a ≠ 0) :
-- imply
  Xor' (a ^ millerRabinD p = 1) (∃ i : ℕ, i < millerRabinS p ∧ a ^ (2 ^ i * millerRabinD p) = -1) := by
-- proof
  haveI : Fact p.Prime := ⟨hp⟩
  have hflt : a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
  rw [millerRabin_decomp p, mul_comm, pow_mul] at hflt
  have h_or := sq_chain_dichotomy (a ^ millerRabinD p) (millerRabinS p) hflt
  have h_not_both : ¬ (a ^ millerRabinD p = 1 ∧
    ∃ i : ℕ, i < millerRabinS p ∧ a ^ (2 ^ i * millerRabinD p) = -1) := by
    rintro ⟨h1, i, his, hi⟩
    have h2 : a ^ (2 ^ i * millerRabinD p) = 1 := by
      rw [mul_comm, pow_mul, h1, one_pow]
    rw [h2] at hi
    have hp2 : p = 2 := by
      by_contra hne
      have : 2 < p := Nat.lt_of_le_of_ne hp.two_le (Ne.symm hne)
      haveI : Fact (2 < p) := ⟨this⟩
      exact CharP.neg_one_ne_one (ZMod p) p hi.symm
    subst hp2
    have : millerRabinS 2 = 0 := by
      simp only [millerRabinS]
      show multiplicity 2 (2 - 1) = 0
      simp only [Nat.reduceSub]
      rw [multiplicity_eq_zero]; omega
    omega
  obtain h_left | ⟨i, hi_lt, hi_eq⟩ := h_or
  · left
    exact ⟨h_left, fun ⟨i, _, _⟩ => h_not_both ⟨h_left, i, ‹_›, ‹_›⟩⟩
  · right
    constructor
    · exact ⟨i, hi_lt, by rw [mul_comm, pow_mul]; exact hi_eq⟩
    · intro h_left
      exact h_not_both ⟨h_left, i, hi_lt, by rw [mul_comm, pow_mul]; exact hi_eq⟩

/--
[millerRabin_witness_liar_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean)
-/
@[path]
lemma millerRabin_witness_liar_card
  {N : ℕ} :
-- imply
  (millerRabinWitnessSet N).card + (millerRabinLiarSet N).card = (Finset.Icc 1 (N - 1)).card :=
-- proof
  Finset.card_filter_add_card_filter_not (IsMillerRabinWitness N)

/--
[zmod_ne_zero_of_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean)
-/
@[path]
lemma zmod_ne_zero_of_mem_Icc
  {N : ℕ}
  {a : ℕ}
-- given
  (hN : N > 1)
  (ha : a ∈ Finset.Icc 1 (N - 1)) :
-- imply
  (a : ZMod N) ≠ 0 := by
-- proof
  haveI : NeZero N := ⟨by omega⟩
  rw [Finset.mem_Icc] at ha
  intro h
  have hval : (a : ZMod N).val = 0 := by rw [h]; simp
  rw [ZMod.val_natCast] at hval
  have hdvd : N ∣ a := Nat.dvd_of_mod_eq_zero hval
  exact absurd (Nat.eq_zero_of_dvd_of_lt hdvd (by omega)) (by omega)

/--
[millerRabin_liar_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean)
-/
@[path]
lemma millerRabin_liar_coprime
  {N : ℕ}
  {a : ℕ}
-- given
  (hN : N > 1)
  (ha_mem : a ∈ millerRabinLiarSet N) :
-- imply
  a.Coprime N := by
-- proof
  simp only [millerRabinLiarSet, Finset.mem_filter] at ha_mem
  obtain ⟨ha_Icc, ha_liar⟩ := ha_mem
  have ha_ne : (a : ZMod N) ≠ 0 := zmod_ne_zero_of_mem_Icc hN ha_Icc
  haveI : NeZero N := ⟨by omega⟩
  rw [← ZMod.isUnit_iff_coprime]
  simp only [IsMillerRabinWitness, not_and, not_forall, not_not, exists_prop] at ha_liar
  have ha_liar' := ha_liar ha_ne
  by_cases hd : (a : ZMod N) ^ millerRabinD N = 1
  ·
    exact IsUnit.of_pow_eq_one hd (by
      simp only [millerRabinD]
      exact Nat.div_pos (Nat.le_of_dvd (by omega) (pow_multiplicity_dvd 2 (N - 1)))
        (Nat.pos_of_ne_zero (by positivity)) |>.ne')
  ·
    have : ∃ r, r < millerRabinS N ∧ (a : ZMod N) ^ (2 ^ r * millerRabinD N) = -1 :=
      (ha_liar' hd)
    obtain ⟨r, _, h_neg⟩ := this
    have h1 : (a : ZMod N) ^ (2 ^ r * millerRabinD N * 2) = 1 := by
      rw [pow_mul, h_neg, neg_one_sq]
    exact IsUnit.of_pow_eq_one h1 (by
      have : 0 < 2 ^ r * millerRabinD N := by
        apply Nat.mul_pos (Nat.pos_of_ne_zero (by positivity))
        exact Nat.div_pos (Nat.le_of_dvd (by omega) (pow_multiplicity_dvd 2 (N - 1)))
          (Nat.pos_of_ne_zero (by positivity))
      omega)
/-- Miller-Rabin liar bound: for an odd composite `N > 1`, at most one quarter
of the elements of `[1, N-1]` are liars. -/

/--
[two_pow_twoAdicVal_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean)
-/
@[path]
lemma two_pow_twoAdicVal_dvd
  {n : ℕ} :
-- imply
  2 ^ twoAdicVal n ∣ n := by
-- proof
  match n with
  | 0 => simp [twoAdicVal]
  | n + 1 =>
    simp only [twoAdicVal]
    split_ifs with h
    · have h2 : 2 ∣ (n + 1) := Nat.dvd_of_mod_eq_zero (by omega)
      have ih := two_pow_twoAdicVal_dvd ((n + 1) / 2)
      rw [pow_add, pow_one]
      exact Nat.mul_dvd_of_dvd_div h2 ih
    · simp
termination_by n
decreasing_by omega

/--
[twoAdicVal_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean)
-/
@[path]
lemma twoAdicVal_decomp
  {n : ℕ} :
-- imply
  n = 2 ^ twoAdicVal n * (n / 2 ^ twoAdicVal n) :=
-- proof
  (Nat.mul_div_cancel' (two_pow_twoAdicVal_dvd n)).symm

/--
[pow_two_pow_eq_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean)
-/
@[path]
lemma pow_two_pow_eq_one_or_neg_one
  [Ring R]
  [NoZeroDivisors R]
  {x : R}
  {n : ℕ}
-- given
  (hx : x ^ 2 ^ n = 1) :
-- imply
  x = 1 ∨ ∃ r : ℕ, r < n ∧ x ^ 2 ^ r = -1 := by
-- proof
  induction n with
  | zero => simp at hx; exact Or.inl hx
  | succ n ih =>
    rw [pow_succ, pow_mul] at hx
    obtain h | h := sq_eq_one_iff.mp hx
    · rcases ih h with h | ⟨r, hr, heq⟩
      · exact Or.inl h
      · exact Or.inr ⟨r, Nat.lt_succ_of_lt hr, heq⟩
    · exact Or.inr ⟨n, lt_add_one n, h⟩

/--
[millerRabin_decompose](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean)
-/
@[path]
lemma millerRabin_decompose
  {N : ℕ} :
-- imply
  N - 1 = 2 ^ millerRabinS N * millerRabinD N :=
-- proof
  millerRabin_decomp N

/--
[millerRabinStep_true_of_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean)
-/
@[path]
lemma millerRabinStep_true_of_prime
  {p : ℕ}
  [hp : Fact p.Prime]
  {a : ℕ}
-- given
  (ha : (a : ZMod p) ≠ 0) :
-- imply
  millerRabinStep p a = true := by
-- proof
  unfold millerRabinStep
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range]
  set s := twoAdicVal (p - 1) with hs_def
  set d := (p - 1) / 2 ^ s with hd_def
  have fermat : (a : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
  have decomp : p - 1 = 2 ^ s * d := twoAdicVal_decomp (p - 1)
  rw [decomp] at fermat
  have key : ((a : ZMod p) ^ d) ^ (2 ^ s) = 1 := by
    rw [← pow_mul, mul_comm]; exact fermat
  obtain h | ⟨r, hr, heq⟩ := pow_two_pow_eq_one_or_neg_one key
  · exact Or.inl h
  · right; exact ⟨r, hr, by rwa [← pow_mul, mul_comm] at heq⟩
section ECPP
open WeierstrassCurve

/--
[not_dvd_of_stronglyNonzeroModN](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean)
-/
@[path]
lemma not_dvd_of_stronglyNonzeroModN
  {Pz : ℤ}
  {N p : ℕ}
-- given
  (hstr : IsStronglyNonzeroModN Pz N)
  (hp : p.Prime)
  (hpN : p ∣ N) :
-- imply
  ¬((p : ℤ) ∣ Pz) := by
-- proof
  unfold IsStronglyNonzeroModN at hstr
  have hgcd : Nat.gcd Pz.natAbs N = 1 := by
    simp [Int.gcd, Int.natAbs_natCast] at hstr; exact hstr
  intro h
  have h1 : p ∣ Pz.natAbs := by rwa [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast] at h
  have h2 : p ∣ Nat.gcd Pz.natAbs N := Nat.dvd_gcd h1 hpN
  rw [hgcd] at h2
  exact absurd (Nat.le_of_dvd Nat.one_pos h2) (Nat.not_le.mpr hp.one_lt)

/--
[isNonzeroModN_of_isStronglyNonzeroModN](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean)
-/
@[path]
lemma isNonzeroModN_of_isStronglyNonzeroModN
  {Pz : ℤ}
  {N : ℕ}
-- given
  (hstr : IsStronglyNonzeroModN Pz N)
  (hN : 1 < N) :
-- imply
  IsNonzeroModN Pz N := by
-- proof
  unfold IsNonzeroModN IsZeroModN
  intro h
  unfold IsStronglyNonzeroModN at hstr
  have hN_dvd_gcd : N ∣ Int.gcd Pz ↑N := by
    simp only [Int.gcd, Int.natAbs_natCast]
    exact Nat.dvd_gcd (Int.natCast_dvd.mp h) (dvd_refl N)
  rw [hstr] at hN_dvd_gcd
  exact absurd (Nat.le_of_dvd Nat.one_pos hN_dvd_gcd) (Nat.not_le.mpr hN)

/--
[isStronglyNonzeroModN_iff_isNonzeroModN_of_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean)
-/
@[path]
lemma isStronglyNonzeroModN_iff_isNonzeroModN_of_prime
  {Pz : ℤ}
  {N : ℕ}
-- given
  (hN : N.Prime) :
-- imply
  IsStronglyNonzeroModN Pz N ↔ IsNonzeroModN Pz N := by
-- proof
  unfold IsStronglyNonzeroModN IsNonzeroModN IsZeroModN
  constructor
  · intro hgcd hdvd
    have hN_dvd_gcd : N ∣ Int.gcd Pz ↑N := by
      simp only [Int.gcd, Int.natAbs_natCast]
      exact Nat.dvd_gcd (Int.natCast_dvd.mp hdvd) (dvd_refl N)
    rw [hgcd] at hN_dvd_gcd
    exact absurd (Nat.le_of_dvd Nat.one_pos hN_dvd_gcd) (Nat.not_le.mpr hN.one_lt)
  · intro hndvd
    simp only [Int.gcd, Int.natAbs_natCast]
    show Nat.Coprime Pz.natAbs N
    exact Nat.Coprime.symm (hN.coprime_iff_not_dvd.mpr (fun h => hndvd (Int.natCast_dvd.mpr h)))

/--
[fourth_root_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean)
-/
@[path]
lemma fourth_root_mono
  {p N : ℕ}
-- given
  (hp2 : p ^ 2 ≤ N) :
-- imply
  (Real.sqrt ↑p + 1) ^ 2 ≤ (Real.sqrt (Real.sqrt ↑N) + 1) ^ 2 := by
-- proof
  have h1 : (p : ℝ) ≤ Real.sqrt ↑N := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg (α := ℝ) p)]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hp2)
  nlinarith [Real.sqrt_le_sqrt h1, Real.sqrt_nonneg (p : ℝ)]

/--
[disc_ne_zero_of_coprime_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean)
-/
@[path]
lemma disc_ne_zero_of_coprime_dvd
  {W : WeierstrassCurve ℤ}
  {N p : ℕ}
-- given
  (hcop : Nat.Coprime N (Int.natAbs W.Δ))
  (hp : p.Prime)
  (hpN : p ∣ N) :
-- imply
  (Int.castRingHom (ZMod p)) W.Δ ≠ 0 := by
-- proof
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  simp only [Int.coe_castRingHom] at h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have h1 : p ∣ W.Δ.natAbs := by
    rwa [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast] at h
  have h2 : p ∣ Nat.gcd N (W.Δ.natAbs) := Nat.dvd_gcd hpN h1
  rw [hcop] at h2
  exact absurd (Nat.le_of_dvd Nat.one_pos h2) (Nat.not_le.mpr hp.one_lt)
/-- Under the Goldwasser-Kilian hypotheses, for any prime `p ∣ N`, the
reduction of the point modulo `p` is annihilated by `M` and not by `M/ℓ`
for any prime `ℓ ∣ M`. -/
end ECPP


-- created on 2026-10-23
