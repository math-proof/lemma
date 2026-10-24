import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.RHorseNumberFubini
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[rHorse_card_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_card_strictMono (r k : ℕ) :
  Nat.card { f : Fin r → Fin k // StrictMono f } = k.choose r := by
  rw [Nat.card_eq_fintype_card,
    Fintype.card_congr (rHorse_strictMonoEquivFinset r k),
    Fintype.card_finset_len, Fintype.card_fin]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorse_card_functions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_card_functions {n r : ℕ} (hrn : r ≤ n) (k : ℕ) :
  Nat.card { f : Fin n → Fin k // rHorseIncreasing hrn f } =
    k.choose r * k ^ (n - r) := by
  rw [Nat.card_congr ((rHorse_conditionEquiv hrn k).trans
    (rHorse_conditionProdEquiv n r k)), Nat.card_prod, rHorse_card_strictMono,
    Nat.card_fun, Nat.card_fin, Nat.card_fin]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorse_card_functions_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_card_functions_eq_sum {n r : ℕ} (hrn : r ≤ n) (k : ℕ) :
  Nat.card { g : Fin n → Fin k // rHorseIncreasing hrn g } =
    ∑ i ∈ Finset.range (k + 1), k.choose i *
      Nat.card { f : Fin n → Fin i // rHorseSurjectiveIncreasing hrn f } := by
  let q := fun g : { g : Fin n → Fin k // rHorseIncreasing hrn g } =>
    Finset.image g.1 Finset.univ
  calc
    Nat.card { g : Fin n → Fin k // rHorseIncreasing hrn g } =
      Nat.card ((s : Finset (Fin k)) ×
        { g : { g : Fin n → Fin k // rHorseIncreasing hrn g } // q g = s }) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv q).symm
    _ = ∑ s : Finset (Fin k),
      Nat.card { g : { g : Fin n → Fin k // rHorseIncreasing hrn g } // q g = s } :=
      Nat.card_sigma
    _ = ∑ s : Finset (Fin k),
      Nat.card { f : Fin n → Fin s.card // rHorseSurjectiveIncreasing hrn f } := by
      apply Finset.sum_congr rfl
      intro s _
      exact Nat.card_congr (rHorse_imageFiberEquiv hrn s)
    _ = ∑ i ∈ Finset.range (k + 1),
      ∑ s ∈ (Finset.univ : Finset (Fin k)).powersetCard i,
        Nat.card { f : Fin n → Fin s.card // rHorseSurjectiveIncreasing hrn f } := by
      simpa only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] using
        Finset.sum_powerset (Finset.univ : Finset (Fin k))
          (fun s => Nat.card
            { f : Fin n → Fin s.card // rHorseSurjectiveIncreasing hrn f })
    _ = ∑ i ∈ Finset.range (k + 1), k.choose i *
      Nat.card { f : Fin n → Fin i // rHorseSurjectiveIncreasing hrn f } := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul] using
        Finset.sum_powersetCard i (Finset.univ : Finset (Fin k))
          (fun j => Nat.card
            { f : Fin n → Fin j // rHorseSurjectiveIncreasing hrn f })

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorse_pow_eq_sum_choose](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_pow_eq_sum_choose (k m : ℕ) :
  k ^ m = ∑ i ∈ Finset.range (m + 1),
    k.choose i * (Nat.factorial i * Nat.stirlingSecond m i) := by
  rw [Nat.pow_eq_sum_stirlingSecond_mul_descFactorial]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorse_sum_choose_stirlingSecond](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_sum_choose_stirlingSecond (k m : ℕ) :
  (∑ i ∈ Finset.range (k + 1),
    k.choose i * (Nat.factorial i * Nat.stirlingSecond m i)) = k ^ m := by
  rw [rHorse_pow_eq_sum_choose]
  obtain hmk | hkm := le_total m k
  · symm
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hmk))
    intro i hik him
    rw [Finset.mem_range] at hik
    simp only [Finset.mem_range, not_lt] at him
    have hmi : m < i := by omega
    rw [Nat.stirlingSecond_eq_zero_of_lt hmi, mul_zero, mul_zero]
  · apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hkm))
    intro i him hik
    rw [Finset.mem_range] at him
    simp only [Finset.mem_range, not_lt] at hik
    have hki : k < i := by omega
    rw [Nat.choose_eq_zero_of_lt hki, zero_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorse_sum_choose_stirlingSecond_rat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_sum_choose_stirlingSecond_rat (k m : ℕ) :
  (∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℚ) *
      ((Nat.factorial i : ℚ) * (Nat.stirlingSecond m i : ℚ))) =
    (k : ℚ) ^ m := by
  exact_mod_cast rHorse_sum_choose_stirlingSecond k m

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorse_pow_eq_sum_stirlingSecond_descFactorial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_pow_eq_sum_stirlingSecond_descFactorial
  (k m N : ℕ) (hmN : m ≤ N) :
  k ^ m = ∑ i ∈ Finset.range (N + 1),
    Nat.stirlingSecond m i * k.descFactorial i := by
  rw [Nat.pow_eq_sum_stirlingSecond_mul_descFactorial]
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hmN))
  intro i hiN him
  simp only [Finset.mem_range, not_lt] at him
  have hmi : m < i := by omega
  rw [Nat.stirlingSecond_eq_zero_of_lt hmi, zero_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorse_pow_eq_sum_stirlingSecond_descFactorial_rat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_pow_eq_sum_stirlingSecond_descFactorial_rat
  (k m N : ℕ) (hmN : m ≤ N) :
  (k : ℚ) ^ m = ∑ i ∈ Finset.range (N + 1),
    (Nat.stirlingSecond m i : ℚ) * (k.descFactorial i : ℚ) := by
  exact_mod_cast rHorse_pow_eq_sum_stirlingSecond_descFactorial k m N hmN

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorse_signedStirling_orthogonal_rat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_signedStirling_orthogonal_rat (r i : ℕ) :
  (∑ m ∈ Finset.range (r + 1),
    (signedStirlingFirst r m : ℚ) * (Nat.stirlingSecond m i : ℚ)) =
    if r = i then 1 else 0 := by
  exact_mod_cast sum_signedStirlingFirst_mul_stirlingSecond r i

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorse_signedStirling_power](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_signedStirling_power (r k : ℕ) :
  (∑ m ∈ Finset.range (r + 1),
    (signedStirlingFirst r m : ℚ) * (k : ℚ) ^ m) =
    (k.descFactorial r : ℚ) := by
  calc
    (∑ m ∈ Finset.range (r + 1),
      (signedStirlingFirst r m : ℚ) * (k : ℚ) ^ m) =
      ∑ m ∈ Finset.range (r + 1), (signedStirlingFirst r m : ℚ) *
        ∑ i ∈ Finset.range (r + 1),
          (Nat.stirlingSecond m i : ℚ) * (k.descFactorial i : ℚ) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mem_range] at hm
      rw [rHorse_pow_eq_sum_stirlingSecond_descFactorial_rat k m r (by omega)]
    _ = ∑ i ∈ Finset.range (r + 1),
      (∑ m ∈ Finset.range (r + 1),
        (signedStirlingFirst r m : ℚ) * (Nat.stirlingSecond m i : ℚ)) *
          (k.descFactorial i : ℚ) := by
      simp_rw [Finset.mul_sum]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = ∑ i ∈ Finset.range (r + 1),
      (if r = i then 1 else 0) * (k.descFactorial i : ℚ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [rHorse_signedStirling_orthogonal_rat]
    _ = (k.descFactorial r : ℚ) := by simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorse_sum_range_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_sum_range_reflect (r : ℕ) (f : ℕ → ℚ) :
  (∑ j ∈ Finset.range (r + 1), f (r - j)) =
    ∑ m ∈ Finset.range (r + 1), f m := by
  refine Finset.sum_bij (fun j _ => r - j) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_range] at hj ⊢
    omega
  · intro j₁ hj₁ j₂ hj₂ h
    rw [Finset.mem_range] at hj₁ hj₂
    omega
  · intro m hm
    rw [Finset.mem_range] at hm
    refine ⟨r - m, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · omega
  · intro j _
    rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorse_signedStirlingFirst_cast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_signedStirlingFirst_cast (r m : ℕ) :
  (signedStirlingFirst r m : ℚ) =
    (-1 : ℚ) ^ (r - m) * (Nat.stirlingFirst r m : ℚ) := by
  rw [signedStirlingFirst_apply]
  push_cast
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorse_falling_stirling](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_falling_stirling (r k : ℕ) :
  (∑ j ∈ Finset.range (r + 1),
    (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
      (k : ℚ) ^ (r - j)) = (k.descFactorial r : ℚ) := by
  calc
    (∑ j ∈ Finset.range (r + 1),
      (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
        (k : ℚ) ^ (r - j)) =
      ∑ j ∈ Finset.range (r + 1),
        (-1 : ℚ) ^ (r - (r - j)) * (Nat.stirlingFirst r (r - j) : ℚ) *
          (k : ℚ) ^ (r - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have hsub : r - (r - j) = j := by omega
      rw [hsub]
    _ = ∑ m ∈ Finset.range (r + 1),
      (-1 : ℚ) ^ (r - m) * (Nat.stirlingFirst r m : ℚ) * (k : ℚ) ^ m :=
      rHorse_sum_range_reflect r
        (fun m => (-1 : ℚ) ^ (r - m) * (Nat.stirlingFirst r m : ℚ) * (k : ℚ) ^ m)
    _ = ∑ m ∈ Finset.range (r + 1),
      (signedStirlingFirst r m : ℚ) * (k : ℚ) ^ m := by
      apply Finset.sum_congr rfl
      intro m _
      rw [rHorse_signedStirlingFirst_cast]
    _ = (k.descFactorial r : ℚ) := rHorse_signedStirling_power r k

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorse_shifted_falling_stirling](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_shifted_falling_stirling {n r : ℕ} (hrn : r ≤ n) (k : ℕ) :
  (∑ j ∈ Finset.range (r + 1),
    (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
      (k : ℚ) ^ (n - j)) =
    (k : ℚ) ^ (n - r) * (k.descFactorial r : ℚ) := by
  calc
    (∑ j ∈ Finset.range (r + 1),
      (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
        (k : ℚ) ^ (n - j)) =
      ∑ j ∈ Finset.range (r + 1),
        (k : ℚ) ^ (n - r) *
          ((-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
            (k : ℚ) ^ (r - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have hsub : n - j = (n - r) + (r - j) := by omega
      rw [hsub, pow_add]
      ring
    _ = (k : ℚ) ^ (n - r) *
      ∑ j ∈ Finset.range (r + 1),
        (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
          (k : ℚ) ^ (r - j) := by
      rw [Finset.mul_sum]
    _ = (k : ℚ) ^ (n - r) * (k.descFactorial r : ℚ) := by
      rw [rHorse_falling_stirling]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorse_candidate_transform](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_candidate_transform {n r : ℕ} (hrn : r ≤ n) (k : ℕ) :
  (∑ i ∈ Finset.range (k + 1), (k.choose i : ℚ) * rHorseCandidate n r i) =
    (k.choose r : ℚ) * (k : ℚ) ^ (n - r) := by
  calc
    (∑ i ∈ Finset.range (k + 1), (k.choose i : ℚ) * rHorseCandidate n r i) =
      (1 / (Nat.factorial r : ℚ)) *
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℚ) *
          ∑ j ∈ Finset.range (r + 1),
            (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
              ((Nat.factorial i : ℚ) * (Nat.stirlingSecond (n - j) i : ℚ)) := by
      unfold rHorseCandidate
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (1 / (Nat.factorial r : ℚ)) *
      ∑ j ∈ Finset.range (r + 1),
        (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
          ∑ i ∈ Finset.range (k + 1),
            (k.choose i : ℚ) *
              ((Nat.factorial i : ℚ) * (Nat.stirlingSecond (n - j) i : ℚ)) := by
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (1 / (Nat.factorial r : ℚ)) *
      ∑ j ∈ Finset.range (r + 1),
        (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
          (k : ℚ) ^ (n - j) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [rHorse_sum_choose_stirlingSecond_rat]
    _ = (1 / (Nat.factorial r : ℚ)) *
      ((k : ℚ) ^ (n - r) * (k.descFactorial r : ℚ)) := by
      rw [rHorse_shifted_falling_stirling hrn k]
    _ = (k.choose r : ℚ) * (k : ℚ) ^ (n - r) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      have hfac : (Nat.factorial r : ℚ) ≠ 0 := by positivity
      rw [one_div_mul_eq_div]
      apply (div_eq_iff hfac).2
      ring

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorse_actual_transform](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_actual_transform {n r : ℕ} (hrn : r ≤ n) (k : ℕ) :
  (∑ i ∈ Finset.range (k + 1),
    (k.choose i : ℚ) *
      (Nat.card
        { f : Fin n → Fin i // rHorseSurjectiveIncreasing hrn f } : ℚ)) =
    (k.choose r : ℚ) * (k : ℚ) ^ (n - r) := by
  have hnat :
    (∑ i ∈ Finset.range (k + 1), k.choose i *
      Nat.card { f : Fin n → Fin i // rHorseSurjectiveIncreasing hrn f }) =
      k.choose r * k ^ (n - r) :=
    (rHorse_card_functions_eq_sum hrn k).symm.trans (rHorse_card_functions hrn k)
  exact_mod_cast hnat

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorse_binomial_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_binomial_injective (a b : ℕ → ℚ)
  (h : ∀ k, (∑ i ∈ Finset.range (k + 1), (k.choose i : ℚ) * a i) =
    ∑ i ∈ Finset.range (k + 1), (k.choose i : ℚ) * b i) :
  ∀ k, a k = b k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hk := h k
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hk
    have hlow : (∑ i ∈ Finset.range k, (k.choose i : ℚ) * a i) =
      ∑ i ∈ Finset.range k, (k.choose i : ℚ) * b i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih i (Finset.mem_range.mp hi)]
    rw [hlow] at hk
    simpa using hk

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorse_card_surjective_eq_candidate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_card_surjective_eq_candidate {n r : ℕ} (hrn : r ≤ n) (i : ℕ) :
  (Nat.card
    { f : Fin n → Fin i // rHorseSurjectiveIncreasing hrn f } : ℚ) =
    rHorseCandidate n r i := by
  apply rHorse_binomial_injective
    (fun k => (Nat.card
      { f : Fin n → Fin k // rHorseSurjectiveIncreasing hrn f } : ℚ))
    (rHorseCandidate n r)
  · intro k
    rw [rHorse_actual_transform hrn k, rHorse_candidate_transform hrn k]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorse_fubini_sum_extend](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
private lemma rHorse_fubini_sum_extend {n j : ℕ} (hj : j ≤ n) :
  (∑ i ∈ Finset.range (n + 1),
    (Nat.factorial i : ℚ) * (Nat.stirlingSecond (n - j) i : ℚ)) =
    (fubiniNumber (n - j) : ℚ) := by
  have hnat :
    (∑ i ∈ Finset.range (n + 1),
      Nat.factorial i * Nat.stirlingSecond (n - j) i) =
      fubiniNumber (n - j) := by
    rw [fubiniNumber_eq_sum]
    calc
      (∑ i ∈ Finset.range (n + 1),
        Nat.factorial i * Nat.stirlingSecond (n - j) i) =
        ∑ i ∈ Finset.range (n + 1),
          Nat.stirlingSecond (n - j) i * Nat.factorial i := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i ∈ Finset.range (n - j + 1),
        Nat.stirlingSecond (n - j) i * Nat.factorial i := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro i hin hij
        simp only [Finset.mem_range, not_lt] at hij
        have hlt : n - j < i := by omega
        rw [Nat.stirlingSecond_eq_zero_of_lt hlt, zero_mul]
  exact_mod_cast hnat

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rHorseNumber_eq_stirlingFirst_sum_fubini](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RHorseNumberFubini.lean)
-/
@[path]
lemma rHorseNumber_eq_stirlingFirst_sum_fubini
  {n r : ℕ}
-- given
  (hrn : r ≤ n) :
-- imply
  ((∑ k ∈ Finset.range (n + 1),
    Nat.card
    { f : Fin n → Fin k //
    Function.Surjective f ∧
    ∀ i j : Fin r, i < j →
    f (Fin.castLE hrn i) < f (Fin.castLE hrn j) }) : ℚ) =
    (1 / (Nat.factorial r : ℚ)) *
    ∑ j ∈ Finset.range (r + 1),
    (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
    (fubiniNumber (n - j) : ℚ) := by
-- proof
  calc
    ((∑ k ∈ Finset.range (n + 1),
      Nat.card
        { f : Fin n → Fin k //
          Function.Surjective f ∧
            ∀ i j : Fin r, i < j →
              f (Fin.castLE hrn i) < f (Fin.castLE hrn j) }) : ℚ) =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.card
          { f : Fin n → Fin k // rHorseSurjectiveIncreasing hrn f } : ℚ) := by
      rfl
    _ = ∑ k ∈ Finset.range (n + 1), rHorseCandidate n r k := by
      apply Finset.sum_congr rfl
      intro k _
      exact rHorse_card_surjective_eq_candidate hrn k
    _ = (1 / (Nat.factorial r : ℚ)) *
      ∑ k ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (r + 1),
          (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
            ((Nat.factorial k : ℚ) * (Nat.stirlingSecond (n - j) k : ℚ)) := by
      unfold rHorseCandidate
      rw [Finset.mul_sum]
    _ = (1 / (Nat.factorial r : ℚ)) *
      ∑ j ∈ Finset.range (r + 1),
        (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
          ∑ k ∈ Finset.range (n + 1),
            (Nat.factorial k : ℚ) * (Nat.stirlingSecond (n - j) k : ℚ) := by
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = (1 / (Nat.factorial r : ℚ)) *
      ∑ j ∈ Finset.range (r + 1),
        (-1 : ℚ) ^ j * (Nat.stirlingFirst r (r - j) : ℚ) *
          (fubiniNumber (n - j) : ℚ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [rHorse_fubini_sum_extend (by omega)]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
