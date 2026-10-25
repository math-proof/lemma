import Mathlib
import sympy.Basic
import Def.NumberTheory.NumberField.Ideal.Counting
open scoped NumberField
open NumberField
open Ideal


namespace NumberField.Ideal

variable (K : Type*) [Field K] [NumberField K]
/--
[two_le_absNorm_of_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean)
-/
@[path]
private lemma two_le_absNorm_of_prime {P : Ideal (𝓞 K)}
  (hprime : P.IsPrime) (hbot : P ≠ ⊥) : 2 ≤ Ideal.absNorm P := by
  have h0 : Ideal.absNorm P ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hbot
  have h1 : Ideal.absNorm P ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr hprime.ne_top
  omega

end NumberField.Ideal

namespace NumberField.Ideal

variable (K : Type*) [Field K] [NumberField K]
/--
[card_normalizedFactors_le_log](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean)
-/
@[path]
private lemma card_normalizedFactors_le_log (M : ℕ) {I : Ideal (𝓞 K)}
  (hI : I ≠ ⊥) (hle : Ideal.absNorm I ≤ M) :
  (UniqueFactorizationMonoid.normalizedFactors I).card ≤ Nat.log 2 M := by
  have hmem : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
    2 ≤ Ideal.absNorm P := by
    intro P hP
    obtain ⟨hprime, hleIP⟩ := (Ideal.mem_normalizedFactors_iff hI).mp hP
    have hPbot : P ≠ ⊥ := by
      rintro rfl
      exact hI (le_bot_iff.mp hleIP)
    exact two_le_absNorm_of_prime K hprime hPbot
  have hmap : ((UniqueFactorizationMonoid.normalizedFactors I).map
    ⇑Ideal.absNorm).prod = Ideal.absNorm I := by
    rw [← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI]
  have htwo : (2 : ℕ) ^ (UniqueFactorizationMonoid.normalizedFactors I).card ≤
    Ideal.absNorm I := by
    have h := Multiset.pow_card_le_prod (s :=
      (UniqueFactorizationMonoid.normalizedFactors I).map ⇑Ideal.absNorm)
      (a := 2) (fun x hx => by
        obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hx
        exact hmem P hP)
    rwa [Multiset.card_map, hmap] at h
  exact Nat.le_log_of_pow_le (by norm_num) (htwo.trans hle)

end NumberField.Ideal

namespace NumberField.Ideal

variable (K : Type*) [Field K] [NumberField K]
/--
[card_primesOver_le_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean)
-/
@[path]
private lemma card_primesOver_le_finrank {p : ℕ} (hp : p.Prime) :
  Nat.card ↥((Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver (𝓞 K)) ≤
    Module.finrank ℚ K := by
  have hcast : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  haveI hprime : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime hcast).mpr (Nat.prime_iff_prime_int.mp hp)
  have hP0 : Ideal.span ({(p : ℤ)} : Set ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hcast
  have hmax : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal :=
    hprime.isMaximal hP0
  rw [Nat.card_eq_fintype_card, ← NumberField.RingOfIntegers.rank,
    ← Ideal.sum_ramification_inertia_eq_finrank
      (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K),
    ← Finset.card_univ, Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun q _ => ?_
  have hq : q.1.IsPrime := q.2.1
  have he : 0 < q.1.ramificationIdx ℤ := Ideal.ramificationIdx_pos q.1 ℤ
  have hf : 0 < q.1.inertiaDeg ℤ := Ideal.inertiaDeg_pos q.1 ℤ
  exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero he.ne' hf.ne')

end NumberField.Ideal

namespace NumberField.Ideal

variable (K : Type*) [Field K] [NumberField K]
/--
[fiberMkAux_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean)
-/
@[path]
omit [NumberField K] in
private lemma fiberMkAux_val {M : ℕ} (p : ℕ) (hprimep : p.Prime)
  (hpleM : p ≤ M) {P : Ideal (𝓞 K)} (hprime : P.IsPrime)
  (hlies : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) :
  (fiberMkAux K p hprimep hpleM hprime hlies).2.1 = P :=
  rfl

end NumberField.Ideal

namespace NumberField.Ideal

variable (K : Type*) [Field K] [NumberField K]
/--
[length_toList_le_log](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean)
-/
@[path]
private lemma length_toList_le_log (M : ℕ)
  (x : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M}) :
  (UniqueFactorizationMonoid.normalizedFactors x.1).toList.length ≤
    Nat.log 2 M := by
  rw [Multiset.length_toList]
  exact card_normalizedFactors_le_log K M x.2.1 x.2.2

end NumberField.Ideal

namespace NumberField.Ideal

variable (K : Type*) [Field K] [NumberField K]
/--
[map_encode_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean)
-/
@[path]
private lemma map_encode_eq (M : ℕ)
  (x : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M})
  (i : Fin (Nat.log 2 M)) :
  (encode K M x i).map (fun F : primeFibers K M => F.2.1) =
    (UniqueFactorizationMonoid.normalizedFactors x.1).toList[i.val]? := by
  by_cases h : i.val <
    (UniqueFactorizationMonoid.normalizedFactors x.1).toList.length
  · unfold encode
    rw [dite_eq_left h]
    simp only [Option.map_some, fiberMkAux_val, List.getElem?_eq_getElem h]
  · have e0 : encode K M x i = none := by
    unfold encode
    exact dite_eq_right h
    rw [e0, Option.map_none]
    exact (List.getElem?_eq_none (le_of_not_gt h)).symm

end NumberField.Ideal

namespace NumberField.Ideal

variable (K : Type*) [Field K] [NumberField K]
/--
[encode_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean)
-/
@[path]
private lemma encode_injective (M : ℕ) :
  Function.Injective (encode K M) := by
  intro x y hxy
  have hlist : (UniqueFactorizationMonoid.normalizedFactors x.1).toList =
    (UniqueFactorizationMonoid.normalizedFactors y.1).toList := by
    apply List.ext_getElem?
    intro n
    by_cases hn : n < Nat.log 2 M
    · have h1 := map_encode_eq K M x ⟨n, hn⟩
      have h2 := map_encode_eq K M y ⟨n, hn⟩
      have h3 := congrFun hxy ⟨n, hn⟩
      rw [h3] at h1
      exact h1.symm.trans h2
    · rw [List.getElem?_eq_none_iff.mpr
      (le_trans (length_toList_le_log K M x) (le_of_not_gt hn)),
      List.getElem?_eq_none_iff.mpr
        (le_trans (length_toList_le_log K M y) (le_of_not_gt hn))]
  have hnf : UniqueFactorizationMonoid.normalizedFactors x.1 =
    UniqueFactorizationMonoid.normalizedFactors y.1 := by
    have hcoe := congrArg (fun l : List (Ideal (𝓞 K)) => (l : Multiset (Ideal (𝓞 K))))
      hlist
    rwa [Multiset.coe_toList, Multiset.coe_toList] at hcoe
  have hI : x.1 = y.1 := by
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self x.2.1]
    conv_rhs => rw [← Ideal.prod_normalizedFactors_eq_self y.2.1]
    rw [hnf]
  exact Subtype.ext hI

end NumberField.Ideal

namespace NumberField.Ideal

variable (K : Type*) [Field K] [NumberField K]
/--
[card_primeBounds_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean)
-/
@[path]
private lemma card_primeBounds_le (M : ℕ) :
  Fintype.card {p : ℕ // p.Prime ∧ p ≤ M} ≤ M - 1 := by
  rw [← Fintype.card_fin (M - 1)]
  refine Fintype.card_le_of_injective
    (fun p : {p : ℕ // p.Prime ∧ p ≤ M} => ⟨p.1 - 2, by
      obtain ⟨hprime, hle⟩ := p.2
      have h2 := hprime.two_le
      omega⟩) ?_
  intro a b hab
  have h2a := a.2.1.two_le
  have h2b := b.2.1.two_le
  have heq : a.1 - 2 = b.1 - 2 := Fin.ext_iff.mp hab
  have hval : a.1 = b.1 := by omega
  exact Subtype.ext hval

end NumberField.Ideal

namespace NumberField.Ideal

variable (K : Type*) [Field K] [NumberField K]
/--
[card_primeFibers_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean)
-/
@[path]
private lemma card_primeFibers_le (M : ℕ) :
  Fintype.card (primeFibers K M) ≤ Module.finrank ℚ K * (M - 1) := by
  classical
  have h1 : ∀ p : {p : ℕ // p.Prime ∧ p ≤ M},
    Fintype.card ↥((Ideal.span ({(p.1 : ℤ)} : Set ℤ)).primesOver (𝓞 K)) ≤
      Module.finrank ℚ K := by
    intro p
    rw [← Nat.card_eq_fintype_card]
    exact card_primesOver_le_finrank K p.2.1
  have hsum : Fintype.card (primeFibers K M)
    = ∑ p : {p : ℕ // p.Prime ∧ p ≤ M},
      Fintype.card ↥((Ideal.span ({(p.1 : ℤ)} : Set ℤ)).primesOver (𝓞 K)) :=
    Fintype.card_sigma
  rw [hsum]
  calc (∑ p : {p : ℕ // p.Prime ∧ p ≤ M},
    Fintype.card ↥((Ideal.span ({(p.1 : ℤ)} : Set ℤ)).primesOver (𝓞 K)))
    ≤ (∑ _p : {p : ℕ // p.Prime ∧ p ≤ M}, Module.finrank ℚ K) :=
      Finset.sum_le_sum fun p _ => h1 p
    _ = Fintype.card {p : ℕ // p.Prime ∧ p ≤ M} • Module.finrank ℚ K := by
      rw [Finset.sum_const, Finset.card_univ]
    _ ≤ (M - 1) • Module.finrank ℚ K := by
      simp only [smul_eq_mul]
      exact mul_le_mul (card_primeBounds_le M) le_rfl (Nat.zero_le _)
        (Nat.zero_le _)
    _ = Module.finrank ℚ K * (M - 1) := by rw [smul_eq_mul, mul_comm]

end NumberField.Ideal

namespace NumberField.Ideal

/--
[card_nonzero_absNorm_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean)
-/
@[path]
lemma card_nonzero_absNorm_le
  [Field K] [NumberField K]
  {M : ℕ} :
-- imply
  Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} ≤
    (Module.finrank ℚ K * M) ^ Nat.log 2 M := by
-- proof
  obtain rfl | hMpos := eq_zero_or_pos M
  · have hempty : IsEmpty
    {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ 0} := by
    constructor
    rintro ⟨I, hbot, hle⟩
    exact (Ideal.absNorm_eq_zero_iff.not.mpr hbot) (Nat.le_zero.mp hle)
    have hfin : Fintype
      {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ 0} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero]
    exact Nat.zero_le _
  · have hM1 : 1 ≤ M := hMpos
    have hfin : Fintype
      {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} := Fintype.ofFinite _
    have hinj : Function.Injective (encode K M) := encode_injective K M
    have hfib := card_primeFibers_le K M
    have hfr : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
    calc Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M}
      = Fintype.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} :=
        Nat.card_eq_fintype_card
      _ ≤ Fintype.card (Fin (Nat.log 2 M) → Option (primeFibers K M)) :=
        Fintype.card_le_of_injective _ hinj
      _ = Nat.card (Fin (Nat.log 2 M) → Option (primeFibers K M)) :=
        Nat.card_eq_fintype_card.symm
      _ = (Nat.card (Option (primeFibers K M))) ^ Nat.card (Fin (Nat.log 2 M)) :=
        Nat.card_fun
      _ = (Fintype.card (primeFibers K M) + 1) ^ Nat.log 2 M := by
        rw [Finite.card_option, Nat.card_eq_fintype_card, Nat.card_fin]
      _ ≤ (Module.finrank ℚ K * M) ^ Nat.log 2 M := by
        apply Nat.pow_le_pow_left _ _
        calc Fintype.card (primeFibers K M) + 1
          ≤ Module.finrank ℚ K * (M - 1) + 1 := Nat.add_le_add_right hfib 1
          _ ≤ Module.finrank ℚ K * (M - 1) + Module.finrank ℚ K :=
            Nat.add_le_add_left hfr _
          _ = Module.finrank ℚ K * ((M - 1) + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
          _ = Module.finrank ℚ K * M := by rw [Nat.sub_add_cancel hM1]

end NumberField.Ideal

namespace NumberField.Ideal

/--
[card_nonzero_absNorm_le_real](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean)
-/
@[path]
lemma card_nonzero_absNorm_le_real
  [Field K] [NumberField K]
  {M : ℝ} :
-- imply
  Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} ≤
    (Module.finrank ℚ K * ⌊M⌋₊) ^ Nat.log 2 ⌊M⌋₊ := by
-- proof
  by_cases hM : 1 ≤ M
  · have hM0 : (0 : ℝ) ≤ M := zero_le_one.trans hM
    have hequiv : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} ≃
      {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ ⌊M⌋₊} :=
      Equiv.subtypeEquivRight fun I => by
        constructor
        · rintro ⟨hbot, hle⟩
          exact ⟨hbot, (Nat.le_floor_iff hM0).mpr hle⟩
        · rintro ⟨hbot, hle⟩
          exact ⟨hbot, (Nat.le_floor_iff hM0).mp hle⟩
    rw [Nat.card_congr hequiv]
    exact card_nonzero_absNorm_le K ⌊M⌋₊
  · have hM' : M < 1 := lt_of_not_ge hM
    have hempty : IsEmpty
      {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} := by
      constructor
      rintro ⟨I, hbot, hle⟩
      have hne : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hbot
      have h1 : (1 : ℝ) ≤ Ideal.absNorm I := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
      linarith
    have hfin : Fintype
      {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} :=
      Fintype.ofIsEmpty
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero]
    exact Nat.zero_le _

end NumberField.Ideal

namespace NumberField.Ideal

/--
[card_nonzero_absNorm_le_real_rpow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Ideal/Counting.lean)
-/
@[path]
lemma card_nonzero_absNorm_le_real_rpow
  [Field K] [NumberField K]
  {M : ℝ}
-- given
  (hM : 0 < M) :
-- imply
  (Nat.card {I : Ideal (𝓞 K) //
    I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} : ℝ) ≤
    ((Module.finrank ℚ K : ℝ) * M) ^ (Real.logb 2 M) := by
-- proof
  by_cases h1M : 1 ≤ M
  · have hNM : (⌊M⌋₊ : ℝ) ≤ M := Nat.floor_le hM.le
    have hN1 : 1 ≤ ⌊M⌋₊ := Nat.le_floor (by exact_mod_cast h1M)
    have hNpos : 0 < ⌊M⌋₊ := by omega
    have hlog : (Nat.log 2 ⌊M⌋₊ : ℝ) ≤ Real.logb 2 M := by
      rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hM]
      rw [Real.rpow_natCast]
      calc
        (2 : ℝ) ^ Nat.log 2 ⌊M⌋₊ = ((2 ^ Nat.log 2 ⌊M⌋₊ : ℕ) : ℝ) := by
          norm_num
        _ ≤ (⌊M⌋₊ : ℝ) := by
          exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt hNpos)
        _ ≤ M := hNM
    have hfinR : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast Module.finrank_pos
    have hfinN : (0 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
    have hbaseNM : (Module.finrank ℚ K : ℝ) * ⌊M⌋₊ ≤
      (Module.finrank ℚ K : ℝ) * M :=
      mul_le_mul_of_nonneg_left hNM hfinN
    have hbase1 : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) * M :=
      one_le_mul_of_one_le_of_one_le hfinR h1M
    have hexpN : (0 : ℝ) ≤ (Nat.log 2 ⌊M⌋₊ : ℝ) := Nat.cast_nonneg _
    have hbaseN : (0 : ℝ) ≤ (Module.finrank ℚ K : ℝ) * ⌊M⌋₊ :=
      mul_nonneg hfinN (Nat.cast_nonneg _)
    have hcast : (Nat.card {I : Ideal (𝓞 K) //
      I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} : ℝ) ≤
      ((Module.finrank ℚ K : ℝ) * ⌊M⌋₊) ^ (Nat.log 2 ⌊M⌋₊ : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast card_nonzero_absNorm_le_real K M
    calc
      (Nat.card {I : Ideal (𝓞 K) //
        I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} : ℝ) ≤
        ((Module.finrank ℚ K : ℝ) * ⌊M⌋₊) ^ (Nat.log 2 ⌊M⌋₊ : ℝ) := hcast
      _ ≤ ((Module.finrank ℚ K : ℝ) * M) ^ (Nat.log 2 ⌊M⌋₊ : ℝ) :=
        Real.rpow_le_rpow hbaseN hbaseNM hexpN
      _ ≤ ((Module.finrank ℚ K : ℝ) * M) ^ (Real.logb 2 M) :=
        Real.rpow_le_rpow_of_exponent_le hbase1 hlog
  · have hM' : M < 1 := lt_of_not_ge h1M
    have hempty : IsEmpty
      {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} := by
      constructor
      rintro ⟨I, hbot, hle⟩
      have hne : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hbot
      have h1 : (1 : ℝ) ≤ Ideal.absNorm I := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
      linarith
    have hfin : Fintype
      {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} :=
      Fintype.ofIsEmpty
    have hcard0 : Nat.card
      {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ M} = 0 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero]
    have hbase : (0 : ℝ) ≤ (Module.finrank ℚ K : ℝ) * M :=
      mul_nonneg (Nat.cast_nonneg _) hM.le
    have hrhs : (0 : ℝ) ≤
      ((Module.finrank ℚ K : ℝ) * M) ^ (Real.logb 2 M) :=
      Real.rpow_nonneg hbase _
    rwa [hcard0, Nat.cast_zero]

end NumberField.Ideal


-- created on 2026-10-20
-- updated on 2026-10-23
