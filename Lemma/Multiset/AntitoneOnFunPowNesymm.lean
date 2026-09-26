import sympy.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Multiset.Fintype
open Polynomial


/-- The normalized elementary symmetric functions: `nesymm s k = s.esymm k / (s.card.choose k)`. -/
noncomputable def nesymm (s : Multiset ℝ) (k : ℕ) : ℝ := s.esymm k / (s.card.choose k)

/-- The `n`th elementary symmetric function of `a ::ₘ s` splits. -/
@[simp]
private lemma esymm_cons (a : ℝ) (s : Multiset ℝ) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp [Multiset.esymm, Multiset.sum_map_mul_left]

@[simp]
private lemma esymm_zero (s : Multiset ℝ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

@[simp]
private lemma esymm_one (s : Multiset ℝ) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one]

private lemma two_mul_esymm_two (s : Multiset ℝ) : 2 * s.esymm 2 =
    s.sum ^ 2 - (s.map (· ^ 2)).sum := by
  induction s using Multiset.induction with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a t ih => grind [Multiset.sum_cons, Multiset.map_cons, esymm_cons, esymm_one]

@[simp]
private lemma esymm_card (s : Multiset ℝ) : s.esymm s.card = s.prod := by
  simp [Multiset.esymm]

@[simp]
private lemma esymm_eq_zero_of_card_lt {s : Multiset ℝ} {k : ℕ} (hk : s.card < k) :
    s.esymm k = 0 := by
  simp [Multiset.esymm, hk]

private lemma esymm_map_inv_aux (s : Multiset ℝ) : 0 ∉ s →
    ∀ j k, s.card = j + k → (s.map (·⁻¹)).esymm k * s.prod = s.esymm j := by
  induction s using Multiset.induction with
  | empty => grind [Multiset.map_zero, Multiset.card_zero]
  | cons a t _ =>
    intro _ j k _
    cases k
    · grind [esymm_zero, esymm_card]
    cases j
    · grind [esymm_zero, Multiset.card_map, esymm_card, Multiset.prod_map_inv',
        Multiset.prod_ne_zero]
    · grind [Multiset.map_cons, esymm_cons, Multiset.prod_cons, Multiset.card_cons]

private lemma esymm_map_inv {s : Multiset ℝ} (h0 : 0 ∉ s) {k : ℕ}
    (hk : k ≤ s.card) : s.esymm k = (s.map (·⁻¹)).esymm (s.card - k) * s.esymm s.card := by
  grind [esymm_map_inv_aux, esymm_card]

/-- Relate a `Multiset.sum` to a sum over `toEnumFinset`. -/
private lemma sum_map_eq_sum_toEnumFinset (m : Multiset ℝ) (f : ℝ → ℝ) :
    (m.map f).sum = ∑ i ∈ m.toEnumFinset, f i.1 := by
  grind [m.map_toEnumFinset_fst, Multiset.map_map, Finset.sum_map_val]

/-- Chebyshev/Cauchy-Schwarz for a multiset: the square of the sum is at most the
cardinality times the sum of squares. -/
private lemma sq_sum_le_card_mul_sum_sq' (m : Multiset ℝ) :
    m.sum ^ 2 ≤ m.card * (m.map (· ^ 2)).sum := by
  have hsum : (m.map id).sum = ∑ i ∈ m.toEnumFinset, i.1 :=
    sum_map_eq_sum_toEnumFinset m id
  have hm : m.sum = ∑ i ∈ m.toEnumFinset, i.1 := by simpa [Multiset.map_id] using hsum
  have hsqsum : (m.map (· ^ 2)).sum = ∑ i ∈ m.toEnumFinset, i.1 ^ 2 :=
    sum_map_eq_sum_toEnumFinset m (· ^ 2 : ℝ → ℝ)
  have hs := sq_sum_le_card_mul_sum_sq (s := m.toEnumFinset) (f := Prod.fst)
  rw [hm, hsqsum, ← m.card_toEnumFinset]
  apply hs


/-- Differentiating `∏ (X + aᵢ)` and reading off Vieta coefficients: the derivative's
coefficients are (shifted) elementary symmetric sums of a multiset `t`. -/
private lemma exists_esymm_derivative {s : Multiset ℝ} {n : ℕ} (hs : s.card = n + 1) :
    ∃ t : Multiset ℝ, t.card = n ∧
      ∀ k ≤ n, (n + 1) * t.esymm k = (n + 1 - k) * s.esymm k := by
  set f : ℝ[X] := (s.map (X + C ·)).prod with hf
  set g : ℝ[X] := C ((n : ℝ) + 1)⁻¹ * f.derivative
  set t := g.roots.map (- ·)
  have : f.natDegree = n + 1 := by
    rw [hf, natDegree_multiset_prod_of_monic]
    · simp [hs, add_comm]
    · grind [Multiset.mem_map, monic_X_add_C]
  have : f.derivative.coeff n = (n : ℝ) + 1 := by
    grind [coeff_derivative, Monic.coeff_natDegree, monic_multiset_prod_of_monic, monic_X_add_C]
  have : f.derivative.natDegree ≤ n := by grind [natDegree_derivative_le]
  have : f.derivative.natDegree ≥ n := le_natDegree_of_ne_zero (by grind)
  have : g.natDegree = n := by grind [natDegree_C_mul]
  have : g.Splits := by grind [splits_iff_card_roots, roots_C_mul, card_roots_le_derivative,
    f.derivative.card_roots', Splits.multisetProd, Multiset.mem_map, Splits.X_add_C]
  have : g = (t.map (X + C ·)).prod := by
    grind [prod_multiset_X_sub_C_of_monic_of_roots_card_eq, splits_iff_card_roots, Multiset.map_map,
      Monic, leadingCoeff]
  have : t.card = n := by grind [Multiset.card_map, splits_iff_card_roots]
  refine ⟨t, this, fun k hk ↦ ?_⟩
  have : ((n - k + 1 : ℕ) : ℝ) = n + 1 - k := by simp [Nat.cast_sub hk]; grind
  have : g.coeff (n - k) = t.esymm k := by grind [Multiset.prod_X_add_C_coeff]
  grind [coeff_derivative, Multiset.prod_X_add_C_coeff]

/-- The derivative reduction, normalized by binomial coefficients. -/
private lemma exists_esymm_div_choose {s : Multiset ℝ} {n : ℕ} (hs : s.card = n + 1) :
    ∃ t : Multiset ℝ, t.card = n ∧
      ∀ k ≤ n, t.esymm k / (n.choose k) = s.esymm k / ((n + 1).choose k) := by
  obtain ⟨t, htc, ht⟩ := exists_esymm_derivative hs
  refine ⟨t, htc, fun k hk ↦ ?_⟩
  rw [div_eq_div_iff]
  · apply mul_left_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0)
    grind [Nat.cast_sub, (mod_cast n.choose_mul_succ_eq k : (n.choose k : ℝ) * (n + 1) =
      ((n + 1).choose k : ℝ) * (n + 1 - k : ℕ))]
  all_goals exact_mod_cast (Nat.choose_pos (by omega)).ne'


/-- The base case of Newton's inequality. -/
private lemma newton_base (s : Multiset ℝ) (n : ℕ) (hs : s.card = n) :
    (n : ℝ) ^ 2 * (2 * s.esymm 2) ≤ (n : ℝ) * ((n : ℝ) - 1) * (s.esymm 1) ^ 2 := by
  subst hs
  rw [esymm_one, two_mul_esymm_two s]
  nlinarith [mul_nonneg s.card.cast_nonneg (sub_nonneg.mpr (sq_sum_le_card_mul_sum_sq' s))]

private lemma newton_aux (n : ℕ) : ∀ s : Multiset ℝ, s.card = n → ∀ k, k + 2 ≤ n →
    nesymm s k * nesymm s (k + 2) ≤ (nesymm s (k + 1)) ^ 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs k hk
    obtain rfl | _ := eq_or_lt_of_le hk
    ·
      if h0 : 0 ∈ s then
        nth_rewrite 2 [nesymm]
        rw [← hs, esymm_card, Multiset.prod_eq_zero h0]
        grind [sq_nonneg]
      else
        have : 2 * (k + 2) * (s.esymm k * s.esymm (k + 2)) ≤ (k + 1) * (s.esymm (k + 1)) ^ 2 := by
          rw [esymm_map_inv h0 (by omega : k + 1 ≤ s.card),
          esymm_map_inv h0 (by omega : k ≤ s.card),
          hs, (by grind : (k + 2) - (k + 1) = 1), (by grind : (k + 2) - k = 2)]
          have := newton_base (s.map (·⁻¹)) (k + 2) (by grind [Multiset.card_map])
          push_cast at this
          nlinarith [sq_nonneg (s.esymm (k + 2))]
        have : ((k + 2).choose k : ℝ) * 2 = (k + 2) * (k + 1) := by
          norm_cast
          rw [← (k + 2).choose_symm (by omega), (by omega : k + 2 - k = 2)]
          obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ := k.even_or_odd <;> grind [Nat.choose_two_right]
        have : ((k + 2).choose (k + 1) : ℝ) = k + 2 := by
          rw [(by rfl : k + 1 = k + 2 - 1), (k + 2).choose_symm (k := 1) (by omega)]
          simp
        unfold nesymm
        field_simp
        rw [hs, this, div_le_div_iff₀ (mod_cast (by grind [Nat.choose_pos])) (by positivity)]
        simp
        nlinarith
    ·
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      grind [nesymm, exists_esymm_div_choose hs]


/-- **Newton's inequality** (normalized form): the normalized elementary symmetric functions are
log-concave. -/
private lemma nesymm_mul_nesymm_le_sq_nesymm (s : Multiset ℝ) (k : ℕ) :
    nesymm s k * nesymm s (k + 2) ≤ (nesymm s (k + 1)) ^ 2 := by
  obtain hk | hk := le_or_gt (k + 2) s.card
  · apply newton_aux s.card s rfl k hk
  ·
    simp only [nesymm, hk, esymm_eq_zero_of_card_lt, zero_div]
    nlinarith

private lemma esymm_succ_eq_zero_of_esymm_eq_zero {s : Multiset ℝ} {k : ℕ}
    (hs : ∀ x ∈ s, 0 ≤ x) (h : s.esymm k = 0) : s.esymm (k + 1) = 0 := by
  rw [Multiset.esymm]
  refine Multiset.sum_eq_zero fun y hy ↦ ?_
  simp only [Multiset.mem_map, Multiset.mem_powersetCard] at hy
  obtain ⟨w, ⟨hws, hwc⟩, rfl⟩ := hy
  obtain ⟨z, hzw⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < w.card)
  obtain ⟨w', rfl⟩ := Multiset.exists_cons_of_mem hzw
  have : w' ∈ s.powersetCard k := (Multiset.mem_powersetCard.mpr ⟨(Multiset.le_cons_self w' z).trans hws,
    by simpa using hwc⟩)
  have {t : Multiset ℝ} (ht : t ∈ s.powersetCard k) : 0 ≤ t.prod :=
    Multiset.prod_nonneg fun z hz ↦ hs z (Multiset.mem_of_le (Multiset.mem_powersetCard.mp ht).1 hz)
  grind [Multiset.prod_cons, le_antisymm, Multiset.single_le_sum, Multiset.mem_map,
    Multiset.mem_map_of_mem, Multiset.esymm]

/-- The elementary symmetric functions of a nonnegative multiset are nonnegative. -/
private lemma esymm_nonneg {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) (k : ℕ) : 0 ≤ s.esymm k := by
  grind [Multiset.esymm, Multiset.sum_nonneg, Multiset.mem_map, Multiset.prod_nonneg,
    Multiset.mem_of_le, Multiset.mem_powersetCard]

/-- The normalized elementary symmetric functions of a nonnegative multiset are nonnegative. -/
private lemma nesymm_nonneg {s : Multiset ℝ} (hs : ∀ x ∈ s, 0 ≤ x) (k : ℕ) : 0 ≤ nesymm s k :=
  div_nonneg (esymm_nonneg hs k) (by positivity)

/-- **Maclaurin's inequality (successor form).** If `s` is nonnegative then
`(nesymm s (k + 1)) ^ k ≤ (nesymm s k) ^ (k + 1)`. -/
private lemma pow_nesymm_le {s : Multiset ℝ} {k : ℕ} (hs : ∀ x ∈ s, 0 ≤ x) :
    (nesymm s (k + 1)) ^ k ≤ (nesymm s k) ^ (k + 1) := by
  obtain hkn | hkn := le_or_gt (k + 1) s.card
  · induction k with
    | zero => simp [nesymm]
    | succ k ih =>
      if hp1 : nesymm s (k + 1) = 0 then
        have : nesymm s (k + 2) = 0 := by
          rw [nesymm, esymm_succ_eq_zero_of_esymm_eq_zero hs, zero_div]
          rw [nesymm, div_eq_zero_iff] at hp1
          apply hp1.resolve_right (mod_cast (Nat.choose_pos (by omega)).ne')
        grind
      else
        have : 0 < (nesymm s (k + 1)) ^ k := by grind [nesymm_nonneg, pow_pos]
        have : (nesymm s (k + 2)) ^ (k + 1) * (nesymm s (k + 1)) ^ k
            ≤ (nesymm s (k + 1)) ^ (k + 2) * (nesymm s (k + 1)) ^ k := calc
            _ ≤ _ := mul_le_mul_of_nonneg_left (ih (by omega)) (pow_nonneg (nesymm_nonneg hs _) _)
            _ = (nesymm s k * nesymm s (k + 2)) ^ (k + 1) := by rw [mul_pow, mul_comm]
            _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (nesymm_nonneg hs _) (nesymm_nonneg hs _))
              (nesymm_mul_nesymm_le_sq_nesymm s k) _
            _ = _ := by rw [← pow_mul, ← pow_add]; grind
        nlinarith
  ·
    rw [nesymm, esymm_eq_zero_of_card_lt (k := k + 1) (by omega)]
    if hk : k = 0 then
      simp_all [nesymm]
    else
      simp only [zero_div, ne_eq, hk, not_false_eq_true, zero_pow]
      positivity [nesymm_nonneg hs k]

/-- **Maclaurin's inequality**(对称平均不等式). For a nonnegative multiset `s`, the sequence
`k ↦ (nesymm s k) ^ (k : ℝ)⁻¹` is antitone for `k ≥ 1`. -/
@[main]
private lemma main {s : Multiset ℝ}
-- given
  (hs : ∀ x ∈ s, 0 ≤ x) :
-- imply
  AntitoneOn (fun k ↦ (nesymm s k) ^ (k : ℝ)⁻¹) {k | 1 ≤ k} := by
-- proof
  rw [← antitone_add_nat_iff_antitoneOn_nat_Ici]
  refine antitone_add_nat_of_succ_le (f := fun k ↦ (nesymm s k) ^ ((k : ℝ)⁻¹)) (fun k _ ↦ ?_)
  have : 0 ≤ nesymm s (k + 1) := nesymm_nonneg hs _
  calc
    _ = ((nesymm s (k + 1)) ^ k) ^ (((k : ℝ) * (k + 1 : ℕ))⁻¹) := by
      rw [← Real.rpow_natCast (nesymm s _) k, ← Real.rpow_mul (by positivity)]
      congr; field_simp
    _ ≤ _ := Real.rpow_le_rpow (pow_nonneg this k) (pow_nesymm_le hs) (by positivity)
    _ = _ := by
      rw [← Real.rpow_natCast (nesymm s k) _, ← Real.rpow_mul (nesymm_nonneg hs _)]
      congr; grind


-- created on 2026-09-23
