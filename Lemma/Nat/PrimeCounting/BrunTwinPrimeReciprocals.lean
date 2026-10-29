import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocals.Part4
open MathlibExt.SelbergSieve
open MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted


namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[card_filter_range_mod_eq_sub_div_abs_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma card_filter_range_mod_eq_sub_div_abs_le (N d a : ℕ) (hd : 0 < d) (ha : a < d) :
  abs ((((Finset.range N).filter (fun n => n % d = a)).card : ℝ) - (N : ℝ) / (d : ℝ)) ≤ 1 := by
  have h1 : Nat.count (fun x => x ≡ a [MOD d]) N = N / d + (if a % d < N % d then 1 else 0) :=
    Nat.count_modEq_card N hd a
  have hmod : a % d = a := Nat.mod_eq_of_lt ha
  have h2 : Nat.count (fun x => x ≡ a [MOD d]) N =
    ((Finset.range N).filter (fun n => n % d = a)).card := by
    rw [Nat.count_eq_card_filter_range]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hmem, h⟩
      refine ⟨hmem, ?_⟩
      have hh : n % d = a % d := h
      rwa [hmod] at hh
    · rintro ⟨hmem, h⟩
      refine ⟨hmem, ?_⟩
      have hh : n % d = a % d := by rw [h, hmod]
      exact hh
  rw [h2] at h1
  rw [hmod] at h1
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hNdecomp : (N:ℝ) = (d:ℝ) * ((N / d : ℕ):ℝ) + ((N % d : ℕ):ℝ) := by
    have h := Nat.div_add_mod N d
    have hc : ((d * (N / d) + N % d : ℕ):ℝ) = (N:ℝ) := by exact_mod_cast h
    push_cast at hc
    linarith [hc]
  have hlt : ((N % d : ℕ):ℝ) < (d:ℝ) := by
    have hnm : N % d < d := Nat.mod_lt N hd
    exact_mod_cast hnm
  have hnn : (0:ℝ) ≤ ((N % d : ℕ):ℝ) := Nat.cast_nonneg _
  have hdiv : (N:ℝ)/(d:ℝ) = ((N / d : ℕ):ℝ) + ((N % d : ℕ):ℝ)/(d:ℝ) := by
    field_simp
    linarith [hNdecomp]
  have hfrac_nonneg : (0:ℝ) ≤ ((N % d : ℕ):ℝ)/(d:ℝ) := div_nonneg hnn (le_of_lt hdR)
  have hfrac_le_one : ((N % d : ℕ):ℝ)/(d:ℝ) ≤ 1 := by
    rw [div_le_one hdR]; exact le_of_lt hlt
  by_cases hif : a < N % d
  · simp only [hif, ↓reduceIte] at h1
    have hcard : ((((Finset.range N).filter (fun n => n % d = a)).card : ℕ):ℝ) =
      ((N / d : ℕ):ℝ) + 1 := by exact_mod_cast h1
    rw [hcard, hdiv]
    rw [show ((N / d : ℕ):ℝ) + 1 - (((N / d : ℕ):ℝ) + ((N % d : ℕ):ℝ)/(d:ℝ)) =
      1 - ((N % d : ℕ):ℝ)/(d:ℝ) by ring]
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  · simp only [hif, ↓reduceIte] at h1
    have hcard : ((((Finset.range N).filter (fun n => n % d = a)).card : ℕ):ℝ) =
      ((N / d : ℕ):ℝ) := by exact_mod_cast h1
    rw [hcard, hdiv]
    rw [show ((N / d : ℕ):ℝ) - (((N / d : ℕ):ℝ) + ((N % d : ℕ):ℝ)/(d:ℝ)) =
      -(((N % d : ℕ):ℝ)/(d:ℝ)) by ring]
    rw [abs_neg, abs_of_nonneg hfrac_nonneg]
    linarith

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brunRho_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brunRho_le (d : ℕ) : brunRho d ≤ d := by
  unfold brunRho
  calc ((Finset.range d).filter _).card ≤ (Finset.range d).card :=
    Finset.card_filter_le _ _
    _ = d := Finset.card_range d

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brunRho_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brunRho_pos (d : ℕ) (hd : 1 ≤ d) : 1 ≤ brunRho d := by
  unfold brunRho
  have hmem : 0 ∈ (Finset.range d).filter (fun a => d ∣ a * (a + 2)) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hd, dvd_zero _⟩
  calc 1 = ({0} : Finset ℕ).card := by simp
    _ ≤ ((Finset.range d).filter _).card := Finset.card_le_card (by simpa using hmem)

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brun_support_inj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brun_support_inj :
  Function.Injective (fun n : ℕ => n * (n + 2)) := by
  apply StrictMono.injective
  intro a b hab
  have hpos : (0 : ℕ) < a + 2 := by omega
  have hbpos : (0 : ℕ) < b := by omega
  have h1 : a * (a + 2) < b * (a + 2) :=
    mul_lt_mul_of_pos_right hab hpos
  have h2 : a + 2 < b + 2 := by omega
  have h3 : b * (a + 2) < b * (b + 2) :=
    mul_lt_mul_of_pos_left h2 hbpos
  exact lt_trans h1 h3

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brunSieve_siftedSum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brunSieve_siftedSum (Y N : ℕ) :
  (brunSieve Y N).siftedSum =
    (((Finset.range N).filter
      (fun n => Nat.Coprime (brunP Y) (n * (n + 2)))).card : ℝ) := by
  unfold BoundingSieve.siftedSum
  change (∑ d ∈ (Finset.range N).image (fun n => n * (n + 2)),
    if Nat.Coprime (brunP Y) d then (1 : ℝ) else 0) = _
  rw [Finset.sum_image brun_support_inj.injOn]
  change (∑ n ∈ Finset.range N,
    if Nat.Coprime (brunP Y) (n * (n + 2)) then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole]

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brunSieve_multSum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brunSieve_multSum (Y N d : ℕ) :
  (brunSieve Y N).multSum d =
    (((Finset.range N).filter
      (fun n => d ∣ n * (n + 2))).card : ℝ) := by
  unfold BoundingSieve.multSum
  change (∑ n ∈ (Finset.range N).image (fun n => n * (n + 2)),
    if d ∣ n then (1 : ℝ) else 0) = _
  rw [Finset.sum_image brun_support_inj.injOn]
  change (∑ n ∈ Finset.range N,
    if d ∣ n * (n + 2) then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole]

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brunSieve_abs_rem_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brunSieve_abs_rem_le (Y N d : ℕ) (hd : 1 ≤ d) :
  abs ((brunSieve Y N).rem d) ≤ (d : ℝ) := by
  have hd0 : d ≠ 0 := by omega
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have htrans : ∀ a : ℕ,
    d ∣ a * (a + 2) ↔ d ∣ (a % d) * ((a % d) + 2) := by
    intro a
    have h1 : a ≡ a % d [MOD d] := (Nat.mod_modEq a d).symm
    have h2 : a + 2 ≡ (a % d) + 2 [MOD d] := Nat.ModEq.add_right 2 h1
    have hmul : a * (a + 2) ≡ (a % d) * ((a % d) + 2) [MOD d] :=
      Nat.ModEq.mul h1 h2
    exact Nat.ModEq.dvd_iff hmul (dvd_refl d)
  set S : Finset ℕ :=
    (Finset.range N).filter (fun n => d ∣ n * (n + 2)) with hS
  set R : Finset ℕ :=
    (Finset.range d).filter (fun a => d ∣ a * (a + 2)) with hR
  have hRcard : R.card = brunRho d := rfl
  have hmaps : (↑S : Set ℕ).MapsTo (fun n => n % d) (↑R) := by
    intro n hn
    simp only [hS, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range] at hn
    obtain ⟨-, hdvd⟩ := hn
    simp only [hR, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨Nat.mod_lt n hdpos, (htrans n).mp hdvd⟩
  have hcard : S.card =
    ∑ a ∈ R, (S.filter (fun n => n % d = a)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber : ∀ a ∈ R, (S.filter (fun n => n % d = a)).card =
    ((Finset.range N).filter (fun n => n % d = a)).card := by
    intro a ha
    simp only [hR, Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨-, hadvd⟩ := ha
    have heq : S.filter (fun n => n % d = a) =
      (Finset.range N).filter (fun n => n % d = a) := by
      ext n
      simp only [hS, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨⟨hmem, -⟩, hmod⟩
        exact ⟨hmem, hmod⟩
      · rintro ⟨hmem, hmod⟩
        refine ⟨⟨hmem, ?_⟩, hmod⟩
        have h1 : d ∣ (n % d) * ((n % d) + 2) := by
          rwa [hmod]
        exact (htrans n).mpr h1
    rw [heq]
  have hbound : ∀ a ∈ R,
    abs ((((S.filter (fun n => n % d = a)).card : ℕ) : ℝ) -
      (N : ℝ) / (d : ℝ)) ≤ 1 := by
    intro a ha
    rw [hfiber a ha]
    simp only [hR, Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨halt, -⟩ := ha
    exact card_filter_range_mod_eq_sub_div_abs_le N d a hdpos halt
  have hmult : (brunSieve Y N).multSum d = (S.card : ℝ) := by
    rw [brunSieve_multSum Y N d, hS]
  have hnu : (brunSieve Y N).nu d = (R.card : ℝ) / (d : ℝ) := by
    change brunNu d = _
    rw [brunNu_apply, hRcard]
  have htotal : (brunSieve Y N).totalMass = (N : ℝ) := rfl
  have hsum_eq : ∑ a ∈ R, (N : ℝ) / (d : ℝ) =
    (R.card : ℝ) / (d : ℝ) * (N : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have hrem_eq : (brunSieve Y N).rem d =
    ∑ a ∈ R, ((((S.filter (fun n => n % d = a)).card : ℕ) : ℝ) -
      (N : ℝ) / (d : ℝ)) := by
    unfold BoundingSieve.rem
    rw [hmult, hnu, htotal, hcard, Nat.cast_sum, ← hsum_eq,
      ← Finset.sum_sub_distrib]
  calc abs ((brunSieve Y N).rem d)
    = abs (∑ a ∈ R, ((((S.filter
      (fun n => n % d = a)).card : ℕ) : ℝ) - (N : ℝ) / (d : ℝ))) := by
      rw [hrem_eq]
    _ ≤ ∑ a ∈ R, abs ((((S.filter
      (fun n => n % d = a)).card : ℕ) : ℝ) - (N : ℝ) / (d : ℝ)) :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ R, (1 : ℝ) := Finset.sum_le_sum hbound
    _ = (R.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (d : ℝ) := by
      rw [hRcard]
      exact_mod_cast brunRho_le d

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brunF_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brunF_nonneg (n : ℕ) : 0 ≤ brunF n := by
  rw [brunF_apply]
  by_cases h : Odd n
  · rw [ite_eq_left h]
    apply div_nonneg _ (Nat.cast_nonneg n)
    norm_cast
    positivity
  · rw [ite_eq_right h]

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brunF_odd_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brunF_odd_prime (p : ℕ) (hp : p.Prime)
  (hp2 : p ≠ 2) : brunF p = 2 / (p : ℝ) := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  rw [brunF_apply, ite_eq_left hodd,
    ArithmeticFunction.cardFactors_apply_prime hp]
  norm_cast

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brunF_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brunF_two : brunF 2 = 0 := by
  rw [brunF_apply, ite_eq_right (by decide : ¬ Odd 2)]

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brunF_norm_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brunF_norm_prime (p : ℕ) (hp : p.Prime) :
  ‖brunF p‖ < 1 := by
  by_cases hp2 : p = 2
  · subst hp2
    rw [brunF_two, norm_zero]
    norm_num
  · have hodd : Odd p := hp.odd_of_ne_two hp2
    rw [brunF_odd_prime p hp hp2, Real.norm_eq_abs]
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
      have h3 : 3 ≤ p := by
        have h2 := hp.two_le
        omega
      exact_mod_cast h3
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 / (p : ℝ))]
    rw [div_lt_one hp0]
    linarith

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brunP_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brunP_ne_zero (Y : ℕ) : brunP Y ≠ 0 := by
  unfold brunP
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  simp only [brunPrimes, Finset.mem_filter, Finset.mem_range] at hp
  obtain ⟨-, hpp, -⟩ := hp
  exact hpp.ne_zero

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brun_divisors_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brun_divisors_card_le (n : ℕ) (hn : n ≠ 0) :
  n.divisors.card ≤ 2 ^ ArithmeticFunction.cardFactors n := by
  have h1 : n.divisors.card =
    ∏ p ∈ n.primeFactors, (n.factorization p + 1) :=
    Nat.card_divisors hn
  have h2 : ArithmeticFunction.cardFactors n =
    ∑ p ∈ n.primeFactors, n.factorization p := by
    rw [ArithmeticFunction.cardFactors_eq_sum_factorization]
    unfold Finsupp.sum
    rw [Nat.support_factorization]
  have h3 : (2 ^ ArithmeticFunction.cardFactors n : ℕ) =
    ∏ p ∈ n.primeFactors, 2 ^ (n.factorization p) := by
    rw [h2, Finset.prod_pow_eq_pow_sum]
  rw [h1, h3]
  apply Finset.prod_le_prod
  intro p _
  exact Nat.lt_two_pow_self

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[sq_oddHarmonic_le_sum_brunF](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma sq_oddHarmonic_le_sum_brunF (Y : ℕ) :
  (oddHarmonic Y) ^ 2 ≤ ∑ n ∈ (Finset.Icc 1 (Y ^ 2)).filter Odd, brunF n := by
  set A : Finset ℕ := (Finset.Icc 1 Y).filter Odd with hA
  set B : Finset ℕ := (Finset.Icc 1 (Y ^ 2)).filter Odd with hB
  have hodd : ∀ n : ℕ, n ∈ B → Odd n := by
    intro n hn
    simp only [hB, Finset.mem_filter, Finset.mem_Icc] at hn
    exact hn.2
  have hBpos : ∀ n : ℕ, n ∈ B → 0 < n := by
    intro n hn
    simp only [hB, Finset.mem_filter, Finset.mem_Icc] at hn
    exact hn.1.1
  -- MapsTo for products
  have hmaps : ∀ p ∈ A ×ˢ A, p.1 * p.2 ∈ B := by
    intro p hp
    simp only [hA, Finset.mem_product, Finset.mem_filter,
      Finset.mem_Icc] at hp
    obtain ⟨⟨⟨h1a, h2a⟩, hoda⟩, ⟨⟨h1b, h2b⟩, hodb⟩⟩ := hp
    simp only [hB, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, hoda.mul hodb⟩
    · exact Nat.mul_pos (by omega) (by omega)
    · calc p.1 * p.2 ≤ Y * Y := Nat.mul_le_mul h2a h2b
      _ = Y ^ 2 := by ring
  -- Square as double sum
  have hsq : (oddHarmonic Y) ^ 2 =
    ∑ p ∈ A ×ˢ A, ((1 : ℝ) / (p.1 : ℝ)) * ((1 : ℝ) / (p.2 : ℝ)) := by
    unfold oddHarmonic
    rw [hA] at *
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  -- Each term equals 1/(a*b)
  have hterm : ∀ p : ℕ × ℕ, ((1 : ℝ) / (p.1 : ℝ)) * ((1 : ℝ) / (p.2 : ℝ)) =
    (1 : ℝ) / (((p.1 * p.2 : ℕ)) : ℝ) := by
    intro p
    rw [div_mul_div_comm, mul_one]
    congr 1
    push_cast
    ring
  rw [hsq]
  simp_rw [hterm]
  -- Fiberwise
  have hfib : (∑ p ∈ A ×ˢ A, (1 : ℝ) / (((p.1 * p.2 : ℕ)) : ℝ)) =
    ∑ n ∈ B, ∑ p ∈ (A ×ˢ A).filter (fun p => p.1 * p.2 = n),
      (1 : ℝ) / (((p.1 * p.2 : ℕ)) : ℝ) := by
    rw [Finset.sum_fiberwise_of_maps_to hmaps]
  rw [hfib]
  apply Finset.sum_le_sum
  intro n hn
  have hnodd : Odd n := hodd n hn
  have hn0 : n ≠ 0 := ne_of_gt (hBpos n hn)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hBpos n hn
  -- Fiber sum equals card / n
  have hfiber_eq : (∑ p ∈ (A ×ˢ A).filter (fun p => p.1 * p.2 = n),
    (1 : ℝ) / (((p.1 * p.2 : ℕ)) : ℝ)) =
    (((A ×ˢ A).filter (fun p => p.1 * p.2 = n)).card : ℝ) / (n : ℝ) := by
    have h1 : ∀ p ∈ (A ×ˢ A).filter (fun p => p.1 * p.2 = n),
      (1 : ℝ) / (((p.1 * p.2 : ℕ)) : ℝ) = (1 : ℝ) / (n : ℝ) := by
      intro p hp
      simp only [Finset.mem_filter] at hp
      obtain ⟨-, hpn⟩ := hp
      rw [hpn]
    rw [Finset.sum_congr rfl h1]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  rw [hfiber_eq]
  have hbrun : brunF n = ((2 ^ ArithmeticFunction.cardFactors n : ℕ) : ℝ) /
    (n : ℝ) := by
    rw [brunF_apply, ite_eq_left hnodd]
    congr 1
    norm_cast
  rw [hbrun]
  -- Card bounds
  have hcard_le : ((A ×ˢ A).filter
    (fun p => p.1 * p.2 = n)).card ≤ n.divisors.card := by
    apply Finset.card_le_card_of_injOn (fun p => p.1)
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter,
        Finset.mem_product] at hp
      obtain ⟨⟨hpa, _⟩, hpn⟩ := hp
      simp only [Finset.mem_coe, Nat.mem_divisors]
      refine ⟨⟨p.2, hpn.symm⟩, hn0⟩
    · intro p1 hp1 p2 hp2 heq
      have heq' : p1.1 = p2.1 := heq
      simp only [Finset.mem_coe, Finset.mem_filter,
        Finset.mem_product] at hp1 hp2
      obtain ⟨⟨hpa1, _⟩, hpn1⟩ := hp1
      obtain ⟨⟨hpa2, _⟩, hpn2⟩ := hp2
      simp only [hA, Finset.mem_filter, Finset.mem_Icc] at hpa1 hpa2
      obtain ⟨⟨h1a1, -⟩, -⟩ := hpa1
      have ha0 : p1.1 ≠ 0 := by omega
      have hb_eq : p1.2 = p2.2 := by
        have h1 : p1.1 * p1.2 = p1.1 * p2.2 := by
          rw [hpn1, heq', hpn2]
        exact Nat.mul_left_cancel (Nat.pos_of_ne_zero ha0) h1
      exact Prod.ext heq' hb_eq
  have hdiv_le : n.divisors.card ≤ 2 ^ ArithmeticFunction.cardFactors n :=
    brun_divisors_card_le n hn0
  have hle : (((A ×ˢ A).filter
    (fun p => p.1 * p.2 = n)).card : ℝ) ≤
    ((2 ^ ArithmeticFunction.cardFactors n : ℕ) : ℝ) := by
    exact_mod_cast le_trans hcard_le hdiv_le
  exact div_le_div_of_nonneg_right hle (le_of_lt hnR)

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[log_add_one_le_two_mul_oddHarmonic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma log_add_one_le_two_mul_oddHarmonic (Y : ℕ) :
  Real.log ((Y : ℝ) + 1) ≤ 2 * oddHarmonic Y := by
  have hlog : Real.log ((Y : ℝ) + 1) ≤ ((harmonic Y : ℚ) : ℝ) := by
    have h := log_add_one_le_harmonic Y
    push_cast at h
    exact h
  have hcast : ((harmonic Y : ℚ) : ℝ) = ∑ i ∈ Finset.Icc 1 Y, (1 : ℝ) / (i : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    congr 1
    ext i
    simp
  rw [hcast] at hlog
  have hsplit : ∑ i ∈ Finset.Icc 1 Y, (1 : ℝ) / (i : ℝ) =
    (∑ i ∈ (Finset.Icc 1 Y).filter Odd, (1 : ℝ) / (i : ℝ)) +
    (∑ i ∈ (Finset.Icc 1 Y).filter (fun i => ¬ Odd i), (1 : ℝ) / (i : ℝ)) := by
    rw [← Finset.sum_filter_add_sum_filter_not _ Odd]
  have hge2 : ∀ i : ℕ, i ∈ (Finset.Icc 1 Y).filter (fun i => ¬ Odd i) → 2 ≤ i := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_Icc] at hi
    obtain ⟨⟨h1, h2⟩, hodd⟩ := hi
    by_contra hc
    push Not at hc
    have : i = 1 := by omega
    subst this
    simp at hodd
  have heven_le : ∑ i ∈ (Finset.Icc 1 Y).filter (fun i => ¬ Odd i), (1 : ℝ) / (i : ℝ) ≤
    ∑ i ∈ (Finset.Icc 1 Y).filter Odd, (1 : ℝ) / (i : ℝ) := by
    have himg : Finset.image (fun i => i - 1) ((Finset.Icc 1 Y).filter (fun i => ¬ Odd i)) ⊆
      (Finset.Icc 1 Y).filter Odd := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc] at hx ⊢
      obtain ⟨i, ⟨⟨h1i, h2i⟩, hiodd⟩, rfl⟩ := hx
      have hi2 := hge2 i (by
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨h1i, h2i⟩, hiodd⟩)
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have heven : Even i := Nat.not_odd_iff_even.mp hiodd
      obtain ⟨k, hk⟩ := heven
      use k - 1
      omega
    calc ∑ i ∈ (Finset.Icc 1 Y).filter (fun i => ¬ Odd i), (1 : ℝ) / (i : ℝ)
      ≤ ∑ i ∈ (Finset.Icc 1 Y).filter (fun i => ¬ Odd i), (1 : ℝ) / ((i - 1 : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi2 := hge2 i hi
        simp only [Finset.mem_filter, Finset.mem_Icc] at hi
        have hle : (i - 1 : ℕ) ≤ i := Nat.sub_le _ _
        have hpos : (0 : ℝ) < ((i - 1 : ℕ) : ℝ) := by
          have : 1 ≤ i - 1 := by omega
          exact_mod_cast this
        apply one_div_le_one_div_of_le hpos (by exact_mod_cast hle)
      _ = ∑ i ∈ Finset.image (fun i => i - 1) ((Finset.Icc 1 Y).filter (fun i => ¬ Odd i)),
        (1 : ℝ) / ((i : ℕ) : ℝ) := by
        rw [Finset.sum_image (by
          intro a ha b hb hab
          have ha2 := hge2 a ha
          have hb2 := hge2 b hb
          simp only at hab
          omega)]
      _ ≤ ∑ i ∈ (Finset.Icc 1 Y).filter Odd, (1 : ℝ) / (i : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg himg
        intro i _ _
        positivity
  change Real.log ((Y : ℝ) + 1) ≤
    2 * (∑ a ∈ (Finset.Icc 1 Y).filter Odd, (1 : ℝ) / (a : ℝ))
  linarith

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

open ArithmeticFunction in
/--
[summable_of_sum_Ico_pow_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma summable_of_sum_Ico_pow_le (f c : ℕ → ℝ) (B : ℕ) (hB : 2 ≤ B)
  (hf : ∀ n, 0 ≤ f n) (hc : Summable c)
  (hblock : ∀ j, ∑ n ∈ Finset.Ico (B ^ j) (B ^ (j + 1)), f n ≤ c j) :
  Summable f := by
  have hBpos : 0 < B := by omega
  have hB1 : 1 < B := by omega
  have hc_nonneg : ∀ j, 0 ≤ c j := by
    intro j
    calc 0 ≤ ∑ n ∈ Finset.Ico (B ^ j) (B ^ (j + 1)), f n :=
      Finset.sum_nonneg (fun n _ => hf n)
      _ ≤ c j := hblock j
  have hrange : ∀ n, ∑ i ∈ Finset.range (B ^ n), f i =
    f 0 + ∑ j ∈ Finset.range n, (∑ k ∈ Finset.Ico (B ^ j) (B ^ (j + 1)), f k) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      have hle : B ^ n ≤ B ^ (n + 1) := Nat.pow_le_pow_right hBpos (Nat.le_succ n)
      have hsplit := Finset.sum_range_add_sum_Ico f hle
      rw [ih] at hsplit
      rw [Finset.sum_range_succ]
      linarith
  refine summable_of_sum_range_le hf (c := f 0 + ∑' j, c j) ?_
  intro n
  have hlt : n < B ^ n := Nat.lt_pow_self hB1
  have hsub : Finset.range n ⊆ Finset.range (B ^ n) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  have hle1 : ∑ i ∈ Finset.range n, f i ≤ ∑ i ∈ Finset.range (B ^ n), f i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hf i)
  have hR := hrange n
  have hle2 : ∑ j ∈ Finset.range n, (∑ k ∈ Finset.Ico (B ^ j) (B ^ (j + 1)), f k) ≤
    ∑ j ∈ Finset.range n, c j := Finset.sum_le_sum (fun j _ => hblock j)
  have hle3 : ∑ j ∈ Finset.range n, c j ≤ ∑' j, c j := by
    apply Summable.sum_le_tsum
    · intro i _
      exact hc_nonneg i
    · exact hc
  linarith

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brun_log_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brun_log_mul_le (j : ℕ) :
  (((j + 1 : ℕ) : ℝ)) * Real.log 2 ≤ 2 * Real.log ((((2 ^ j : ℕ)) : ℝ) + 1) := by
  have htpos : (0 : ℝ) < ((((2 ^ j : ℕ)) : ℝ)) := by
    have h : (0 : ℕ) < 2 ^ j := Nat.pow_pos (by norm_num)
    exact_mod_cast h
  have ht1pos : (0 : ℝ) < ((((2 ^ j : ℕ)) : ℝ) + 1) := by linarith
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ (j + 1) := by positivity
  have hcast : ((((2 ^ j : ℕ)) : ℝ)) = (2 : ℝ) ^ j := by
    push_cast
    ring
  have hsq_ge : (2 : ℝ) ^ (j + 1) ≤ ((((2 ^ j : ℕ)) : ℝ) + 1) ^ 2 := by
    rw [hcast]
    have hpow_succ : (2 : ℝ) ^ (j + 1) = 2 * (2 : ℝ) ^ j := by
      rw [pow_succ]
      ring
    rw [hpow_succ]
    have hsq : ((2 : ℝ) ^ j + 1) ^ 2 = ((2 : ℝ) ^ j) ^ 2 + 2 * (2 : ℝ) ^ j + 1 := by
      ring
    rw [hsq]
    have hnonneg : (0 : ℝ) ≤ ((2 : ℝ) ^ j) ^ 2 + 1 := by positivity
    linarith
  have hlog := Real.log_le_log hpowpos hsq_ge
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog ⊢
  exact hlog

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brun_pow24_div_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brun_pow24_div_le (j : ℕ) :
  (2 : ℝ) ^ (24 * j) / (2 : ℝ) ^ (32 * j) ≤ (1 / 2 : ℝ) ^ j := by
  have hRHS : (1 / 2 : ℝ) ^ j = 1 / (2 : ℝ) ^ j := by
    rw [div_pow, one_pow]
  rw [hRHS]
  have hpos32 : (0 : ℝ) < (2 : ℝ) ^ (32 * j) := by positivity
  have hposj : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  rw [div_le_div_iff₀ hpos32 hposj]
  rw [one_mul, ← pow_add]
  have hexp : 24 * j + j ≤ 32 * j := by omega
  exact pow_le_pow_right₀ (by norm_num) hexp

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brun_pow2_add_one_div_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brun_pow2_add_one_div_le (j : ℕ) :
  ((2 : ℝ) ^ (2 * j) + 1) / (2 : ℝ) ^ (32 * j) ≤ 2 * ((1 / 2 : ℝ) ^ j) := by
  have hRHS : (1 / 2 : ℝ) ^ j = 1 / (2 : ℝ) ^ j := by
    rw [div_pow, one_pow]
  have hpos32 : (0 : ℝ) < (2 : ℝ) ^ (32 * j) := by positivity
  have hposj : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have h1 : (2 : ℝ) ^ (2 * j) / (2 : ℝ) ^ (32 * j) ≤ (1 / 2 : ℝ) ^ j := by
    rw [hRHS, div_le_div_iff₀ hpos32 hposj, one_mul, ← pow_add]
    have hexp : 2 * j + j ≤ 32 * j := by omega
    exact pow_le_pow_right₀ (by norm_num) hexp
  have h2 : (1 : ℝ) / (2 : ℝ) ^ (32 * j) ≤ (1 / 2 : ℝ) ^ j := by
    rw [hRHS]
    have hle : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (32 * j) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact one_div_le_one_div_of_le hposj hle
  have hadd : ((2 : ℝ) ^ (2 * j) + 1) / (2 : ℝ) ^ (32 * j) =
    (2 : ℝ) ^ (2 * j) / (2 : ℝ) ^ (32 * j) + 1 / (2 : ℝ) ^ (32 * j) := by
    rw [add_div]
  rw [hadd]
  have hsum : (2 : ℝ) ^ (2 * j) / (2 : ℝ) ^ (32 * j) + 1 / (2 : ℝ) ^ (32 * j) ≤
    (1 / 2 : ℝ) ^ j + (1 / 2 : ℝ) ^ j := add_le_add h1 h2
  linarith [hsum]

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brun_cast_Y_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brun_cast_Y_sq (j : ℕ) :
  ((((2 ^ j : ℕ)) : ℝ)) ^ 2 = (2 : ℝ) ^ (2 * j) := by
  have hcast : ((((2 ^ j : ℕ)) : ℝ)) = (2 : ℝ) ^ j := by
    push_cast
    ring
  rw [hcast, ← pow_mul, mul_comm j 2]

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brun_cast_Y_pow24](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brun_cast_Y_pow24 (j : ℕ) :
  ((((2 ^ j : ℕ)) : ℝ)) ^ 24 = (2 : ℝ) ^ (24 * j) := by
  have hcast : ((((2 ^ j : ℕ)) : ℝ)) = (2 : ℝ) ^ j := by
    push_cast
    ring
  rw [hcast, ← pow_mul, mul_comm j 24]

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

namespace MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brun_cast_Bj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brun_cast_Bj (j : ℕ) :
  (((((2 ^ 32 : ℕ) ^ j : ℕ)) : ℝ)) = (2 : ℝ) ^ (32 * j) := by
  have hB : ((((2 ^ 32 : ℕ)) : ℝ)) = (2 : ℝ) ^ 32 := by
    push_cast
    ring
  have h1 : (((((2 ^ 32 : ℕ) ^ j : ℕ)) : ℝ)) = ((((2 ^ 32 : ℕ)) : ℝ)) ^ j := by
    rw [Nat.cast_pow]
  rw [h1, hB, ← pow_mul]

end MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted

/--
[brun_twin_prime_reciprocal_series_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/BrunTwinPrimeReciprocals.lean)
-/
@[path]
private lemma brun_twin_prime_reciprocal_series_summable_eq
  :
-- imply
  Summable (fun p : ℕ =>
    if p.Prime ∧ (p + 2).Prime then
    (1 : ℝ) / (p : ℝ) + (1 : ℝ) / ((p + 2 : ℕ) : ℝ)
    else 0) := by
-- proof
  apply MathlibExt.NumberTheory.PrimeCounting.BrunTwinPrimeReciprocalsWanted.brun_twin_prime_reciprocal_series_summable


-- created on 2026-10-20
-- updated on 2026-10-28
