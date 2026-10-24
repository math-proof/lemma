import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Hypercontractivity
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Hypercontractivity
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.TwoPointInequality
import sympy.atlas.v1.Atlas.BooleanFunctions.code.TwoPointInequality
open Finset BigOperators Real


namespace BooleanFourier

/--
[noiseOp_snoc_eq_twoPointNoiseOp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/BonamilBeckner.lean)
-/
@[path]
lemma noiseOp_snoc_eq_twoPointNoiseOp
  {m : ℕ}
  {ρ : ℝ}
  {f : BoolFn (m + 1)}
  {x' : Fin m → Bool}
  {b : Bool} :
-- imply
  noiseOp ρ f (Fin.snoc x' b) = twoPointNoiseOp ρ (fun c => noiseOp ρ (restrictLast f c) x') b := by
-- proof
  simp only [noiseOp, twoPointNoiseOp, restrictLast]
  rw [sum_finBool_succ_split]
  simp_rw [Fin.prod_univ_castSucc]
  simp_rw [Fin.snoc_castSucc, Fin.snoc_last]
  cases b <;> simp only [boolToReal_true, boolToReal_false, ite_true, ite_false, Bool.false_eq_true]
  all_goals (simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]; congr 1; funext y'; ring)
set_option maxHeartbeats 800000 in

end BooleanFourier

namespace BooleanFourier

/--
[lpNorm_convex_combination](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/BonamilBeckner.lean)
-/
@[path]
lemma lpNorm_convex_combination
  {m : ℕ}
  {g₁ g₂ : BoolFn m}
  {α β : ℝ}
  {q : ℝ}
-- given
  (hα : 0 ≤ α)
  (hβ : 0 ≤ β)
  (hq : 1 ≤ q) :
-- imply
  lpNorm q (fun x => α * g₁ x + β * g₂ x) ≤ α * lpNorm q g₁ + β * lpNorm q g₂ := by
-- proof
  unfold lpNorm
  have hq_pos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have h1q_nn : (0 : ℝ) ≤ 1 / q := by positivity
  have habs_bound : ∀ x : Fin m → Bool,
    |α * g₁ x + β * g₂ x| ^ q ≤ (α * |g₁ x| + β * |g₂ x|) ^ q := by
    intro x
    apply Real.rpow_le_rpow (abs_nonneg _) _ hq_pos.le
    calc |α * g₁ x + β * g₂ x|
      ≤ |α * g₁ x| + |β * g₂ x| := abs_add_le _ _
      _ = α * |g₁ x| + β * |g₂ x| := by
        rw [abs_mul, abs_of_nonneg hα, abs_mul, abs_of_nonneg hβ]
  have hsum_bound : (∑ x : Fin m → Bool, |α * g₁ x + β * g₂ x| ^ q) ≤
    (∑ x : Fin m → Bool, (α * |g₁ x| + β * |g₂ x|) ^ q) :=
    Finset.sum_le_sum (fun x _ => habs_bound x)
  have hMinkowski := Real.Lp_add_le_of_nonneg Finset.univ hq
    (fun i _ => mul_nonneg hα (abs_nonneg (g₁ i)))
    (fun i _ => mul_nonneg hβ (abs_nonneg (g₂ i)))
  have hpull_alpha : ∑ i : Fin m → Bool, (α * |g₁ i|) ^ q =
    α ^ q * ∑ i : Fin m → Bool, |g₁ i| ^ q := by
    simp_rw [Real.mul_rpow hα (abs_nonneg _)]; rw [Finset.mul_sum]
  have hpull_beta : ∑ i : Fin m → Bool, (β * |g₂ i|) ^ q =
    β ^ q * ∑ i : Fin m → Bool, |g₂ i| ^ q := by
    simp_rw [Real.mul_rpow hβ (abs_nonneg _)]; rw [Finset.mul_sum]
  rw [hpull_alpha, hpull_beta] at hMinkowski
  have hsimp_alpha : (α ^ q * ∑ i : Fin m → Bool, |g₁ i| ^ q) ^ (1 / q) =
    α * (∑ i : Fin m → Bool, |g₁ i| ^ q) ^ (1 / q) := by
    rw [Real.mul_rpow (rpow_nonneg hα q)
      (Finset.sum_nonneg (fun x _ => rpow_nonneg (abs_nonneg _) _))]
    congr 1
    rw [← rpow_mul hα, mul_one_div_cancel (ne_of_gt hq_pos), rpow_one]
  have hsimp_beta : (β ^ q * ∑ i : Fin m → Bool, |g₂ i| ^ q) ^ (1 / q) =
    β * (∑ i : Fin m → Bool, |g₂ i| ^ q) ^ (1 / q) := by
    rw [Real.mul_rpow (rpow_nonneg hβ q)
      (Finset.sum_nonneg (fun x _ => rpow_nonneg (abs_nonneg _) _))]
    congr 1
    rw [← rpow_mul hβ, mul_one_div_cancel (ne_of_gt hq_pos), rpow_one]
  rw [hsimp_alpha, hsimp_beta] at hMinkowski
  have h2m_factor : ∀ (S : ℝ), 0 ≤ S →
    (1 / (2 ^ m : ℝ) * S) ^ (1 / q) = (1 / (2 ^ m : ℝ)) ^ (1 / q) * S ^ (1 / q) :=
    fun S hS => Real.mul_rpow (by positivity) hS
  rw [h2m_factor _ (Finset.sum_nonneg (fun x _ => rpow_nonneg (abs_nonneg _) _))]
  rw [show α * ((1 / (2 ^ m : ℝ)) * ∑ x, |g₁ x| ^ q) ^ (1 / q) +
    β * ((1 / (2 ^ m : ℝ)) * ∑ x, |g₂ x| ^ q) ^ (1 / q) =
    (1 / (2 ^ m : ℝ)) ^ (1 / q) *
      (α * (∑ x, |g₁ x| ^ q) ^ (1 / q) + β * (∑ x, |g₂ x| ^ q) ^ (1 / q)) from by
    rw [h2m_factor _ (Finset.sum_nonneg (fun x _ => rpow_nonneg (abs_nonneg _) _))]
    rw [h2m_factor _ (Finset.sum_nonneg (fun x _ => rpow_nonneg (abs_nonneg _) _))]
    ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact le_trans (rpow_le_rpow (Finset.sum_nonneg (fun x _ => rpow_nonneg (abs_nonneg _) _))
    hsum_bound h1q_nn) hMinkowski
set_option maxHeartbeats 1600000 in

end BooleanFourier

namespace BooleanFourier

/--
[bonami_beckner_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/BonamilBeckner.lean)
-/
@[path]
lemma bonami_beckner_succ
  {m : ℕ}
  {f : BoolFn (m + 1)}
  {p q ρ : ℝ}
-- given
  (hp : 1 ≤ p)
  (hpq : p ≤ q)
  (hρ0 : 0 ≤ ρ)
  (hρ : ρ ≤ Real.sqrt ((p - 1) / (q - 1)))
  (ih : ∀ (g : BoolFn m), lpNorm q (noiseOp ρ g) ≤ lpNorm p g) :
-- imply
  lpNorm q (noiseOp ρ f) ≤ lpNorm p f := by
-- proof
  have hp_pos : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hq_pos : (0 : ℝ) < q := lt_of_lt_of_le hp_pos hpq
  have hq1 : (1 : ℝ) ≤ q := le_trans hp hpq
  set A := lpNorm p (restrictLast f true)
  set B := lpNorm p (restrictLast f false)
  set h : Bool → ℝ := fun c => if c then A else B
  have htwoPointLpNorm_eq : twoPointLpNorm p h = lpNorm p f := by
    unfold twoPointLpNorm
    simp only [h, ite_true]
    have hA_nonneg : 0 ≤ A := by simp only [A]; unfold lpNorm; positivity
    have hB_nonneg : 0 ≤ B := by simp only [B]; unfold lpNorm; positivity
    simp only [ite_false, Bool.false_eq_true]
    rw [abs_of_nonneg hA_nonneg, abs_of_nonneg hB_nonneg]
    have hrl := lpNorm_restrictLast f hp_pos
    have hlpf_nonneg : 0 ≤ lpNorm p f := by unfold lpNorm; positivity
    rw [show (A ^ p + B ^ p) / 2 = (lpNorm p f) ^ p from by linarith [hrl]]
    rw [← rpow_mul hlpf_nonneg, mul_one_div_cancel (ne_of_gt hp_pos), rpow_one]
  have h_two_pt : twoPointLpNorm q (twoPointNoiseOp ρ h) ≤ twoPointLpNorm p h :=
    two_point_inequality hp hpq hρ0 hρ h
  suffices hmain : lpNorm q (noiseOp ρ f) ≤ twoPointLpNorm q (twoPointNoiseOp ρ h) by
    calc lpNorm q (noiseOp ρ f)
      ≤ twoPointLpNorm q (twoPointNoiseOp ρ h) := hmain
      _ ≤ twoPointLpNorm p h := h_two_pt
      _ = lpNorm p f := htwoPointLpNorm_eq
  have hlpq_eq_twoPoint : lpNorm q (noiseOp ρ f) =
    twoPointLpNorm q (fun b => lpNorm q (restrictLast (noiseOp ρ f) b)) := by
    unfold twoPointLpNorm
    have hXT_nn : 0 ≤ lpNorm q (restrictLast (noiseOp ρ f) true) := by unfold lpNorm; positivity
    have hXF_nn : 0 ≤ lpNorm q (restrictLast (noiseOp ρ f) false) := by unfold lpNorm; positivity
    rw [abs_of_nonneg hXT_nn, abs_of_nonneg hXF_nn]
    have hrl := lpNorm_restrictLast (noiseOp ρ f) hq_pos
    have hlhs_nn : 0 ≤ lpNorm q (noiseOp ρ f) := by unfold lpNorm; positivity
    symm
    rw [show (lpNorm q (restrictLast (noiseOp ρ f) true) ^ q +
      lpNorm q (restrictLast (noiseOp ρ f) false) ^ q) / 2 =
      (lpNorm q (noiseOp ρ f)) ^ q from by linarith [hrl]]
    rw [← rpow_mul hlhs_nn, mul_one_div_cancel (ne_of_gt hq_pos), rpow_one]
  rw [hlpq_eq_twoPoint]
  have hρ_half_pos : 0 ≤ (1 + ρ) / 2 := by linarith
  have hρ_half_pos' : 0 ≤ (1 - ρ) / 2 := by
    have hρ_le_1 : ρ ≤ 1 := by
      have h1 : (0 : ℝ) ≤ (p - 1) / (q - 1) := div_nonneg (by linarith) (by linarith)
      have h2 : (p - 1) / (q - 1) ≤ 1 := by
        by_cases hq1' : q = 1
        · simp [hq1', show p = 1 from le_antisymm (hq1' ▸ hpq) hp]
        · rw [div_le_one (by linarith [lt_of_le_of_ne (le_trans hp hpq) (Ne.symm hq1')])]; linarith
      calc ρ ≤ Real.sqrt ((p - 1) / (q - 1)) := hρ
        _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h2
        _ = 1 := Real.sqrt_one
    linarith
  have hih_true : lpNorm q (noiseOp ρ (restrictLast f true)) ≤ A := ih _
  have hih_false : lpNorm q (noiseOp ρ (restrictLast f false)) ≤ B := ih _
  have hft_nn : 0 ≤ lpNorm q (noiseOp ρ (restrictLast f true)) := by unfold lpNorm; positivity
  have hff_nn : 0 ≤ lpNorm q (noiseOp ρ (restrictLast f false)) := by unfold lpNorm; positivity
  have hbound_true : lpNorm q (restrictLast (noiseOp ρ f) true) ≤ twoPointNoiseOp ρ h true := by
    have hfunext : (fun x' => restrictLast (noiseOp ρ f) true x') =
      (fun x' => (1 + ρ) / 2 * noiseOp ρ (restrictLast f true) x' +
        (1 - ρ) / 2 * noiseOp ρ (restrictLast f false) x') := by
      ext x'
      have := noiseOp_snoc_eq_twoPointNoiseOp ρ f x' true
      simp only [restrictLast, twoPointNoiseOp, ite_true] at this ⊢
      exact this
    rw [show lpNorm q (restrictLast (noiseOp ρ f) true) =
      lpNorm q (fun x' => (1 + ρ) / 2 * noiseOp ρ (restrictLast f true) x' +
        (1 - ρ) / 2 * noiseOp ρ (restrictLast f false) x') from by
      exact congrArg (lpNorm q) hfunext]
    calc lpNorm q (fun x' => (1 + ρ) / 2 * noiseOp ρ (restrictLast f true) x' +
      (1 - ρ) / 2 * noiseOp ρ (restrictLast f false) x')
      ≤ (1 + ρ) / 2 * lpNorm q (noiseOp ρ (restrictLast f true)) +
        (1 - ρ) / 2 * lpNorm q (noiseOp ρ (restrictLast f false)) :=
        lpNorm_convex_combination _ _ _ _ hρ_half_pos hρ_half_pos' hq1
      _ ≤ (1 + ρ) / 2 * A + (1 - ρ) / 2 * B := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hih_true hρ_half_pos
        · exact mul_le_mul_of_nonneg_left hih_false hρ_half_pos'
      _ = twoPointNoiseOp ρ h true := by
        simp [twoPointNoiseOp, h]
  have hbound_false : lpNorm q (restrictLast (noiseOp ρ f) false) ≤ twoPointNoiseOp ρ h false := by
    have hfunext : (fun x' => restrictLast (noiseOp ρ f) false x') =
      (fun x' => (1 - ρ) / 2 * noiseOp ρ (restrictLast f true) x' +
        (1 + ρ) / 2 * noiseOp ρ (restrictLast f false) x') := by
      ext x'
      have := noiseOp_snoc_eq_twoPointNoiseOp ρ f x' false
      simp only [restrictLast, twoPointNoiseOp, ite_false, Bool.false_eq_true] at this ⊢
      exact this
    rw [show lpNorm q (restrictLast (noiseOp ρ f) false) =
      lpNorm q (fun x' => (1 - ρ) / 2 * noiseOp ρ (restrictLast f true) x' +
        (1 + ρ) / 2 * noiseOp ρ (restrictLast f false) x') from by
      exact congrArg (lpNorm q) hfunext]
    calc lpNorm q (fun x' => (1 - ρ) / 2 * noiseOp ρ (restrictLast f true) x' +
      (1 + ρ) / 2 * noiseOp ρ (restrictLast f false) x')
      ≤ (1 - ρ) / 2 * lpNorm q (noiseOp ρ (restrictLast f true)) +
        (1 + ρ) / 2 * lpNorm q (noiseOp ρ (restrictLast f false)) :=
        lpNorm_convex_combination _ _ _ _ hρ_half_pos' hρ_half_pos hq1
      _ ≤ (1 - ρ) / 2 * A + (1 + ρ) / 2 * B := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hih_true hρ_half_pos'
        · exact mul_le_mul_of_nonneg_left hih_false hρ_half_pos
      _ = twoPointNoiseOp ρ h false := by
        simp [twoPointNoiseOp, h]
  unfold twoPointLpNorm
  have hXT_nn : 0 ≤ lpNorm q (restrictLast (noiseOp ρ f) true) := by unfold lpNorm; positivity
  have hXF_nn : 0 ≤ lpNorm q (restrictLast (noiseOp ρ f) false) := by unfold lpNorm; positivity
  have hTNoiseT_nn : 0 ≤ twoPointNoiseOp ρ h true := by
    simp [twoPointNoiseOp, h]
    linarith [mul_nonneg hρ_half_pos (by simp only [A]; unfold lpNorm; positivity : (0 : ℝ) ≤ A),
      mul_nonneg hρ_half_pos' (by simp only [B]; unfold lpNorm; positivity : (0 : ℝ) ≤ B)]
  have hTNoiseF_nn : 0 ≤ twoPointNoiseOp ρ h false := by
    simp [twoPointNoiseOp, h]
    linarith [mul_nonneg hρ_half_pos' (by simp only [A]; unfold lpNorm; positivity : (0 : ℝ) ≤ A),
      mul_nonneg hρ_half_pos (by simp only [B]; unfold lpNorm; positivity : (0 : ℝ) ≤ B)]
  rw [abs_of_nonneg hXT_nn, abs_of_nonneg hXF_nn,
    abs_of_nonneg hTNoiseT_nn, abs_of_nonneg hTNoiseF_nn]
  apply rpow_le_rpow (by positivity) _ (by positivity : (0 : ℝ) ≤ 1 / q)
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) < 2).le
  apply add_le_add
  · exact rpow_le_rpow hXT_nn hbound_true hq_pos.le
  · exact rpow_le_rpow hXF_nn hbound_false hq_pos.le

end BooleanFourier

namespace BooleanFourier

/--
[bonami_beckner](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/BonamilBeckner.lean)
-/
@[path]
lemma bonami_beckner
  {n : ℕ}
  {f : BoolFn n}
  {p q ρ : ℝ}
-- given
  (hp : 1 ≤ p)
  (hpq : p ≤ q)
  (hρ0 : 0 ≤ ρ)
  (hρ : ρ ≤ Real.sqrt ((p - 1) / (q - 1))) :
-- imply
  lpNorm q (noiseOp ρ f) ≤ lpNorm p f := by
-- proof
  induction n with
  | zero =>
    unfold lpNorm noiseOp
    simp only [pow_zero, one_div]
    norm_num
    have hq_pos : (0 : ℝ) < q := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hp) hpq
    have hp_pos : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
    exact le_of_eq (by
      have key : ∀ (a : ℝ) (r : ℝ), 0 ≤ a → 0 < r → (a ^ r) ^ r⁻¹ = a := by
        intro a r ha hr
        rw [← rpow_mul ha, mul_inv_cancel₀ (ne_of_gt hr), rpow_one]
      rw [key _ q (abs_nonneg _) hq_pos, key _ p (abs_nonneg _) hp_pos])
  | succ m ih =>
    exact bonami_beckner_succ f hp hpq hρ0 hρ ih

end BooleanFourier

namespace BooleanFourier

/--
[lpNorm_degree1_hypercontractive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/BonamilBeckner.lean)
-/
@[path]
lemma lpNorm_degree1_hypercontractive
  {n : ℕ}
  {f : BoolFn n}
  {q : ℝ}
-- given
  (hd : degree f ≤ 1)
  (hq : 2 ≤ q) :
-- imply
  lpNorm q f ≤ Real.sqrt (q - 1) * lpNorm 2 f := by
-- proof
  have h_bb : ∀ (g : BoolFn n) (ρ' : ℝ),
    0 ≤ ρ' → ρ' ≤ Real.sqrt ((2 - 1) / (q - 1)) →
    lpNorm q (noiseOp ρ' g) ≤ lpNorm 2 g := by
    intro g ρ' hρ'_nonneg hρ'_bound
    exact bonami_beckner g (by norm_num : (1 : ℝ) ≤ 2) (by linarith) hρ'_nonneg
      hρ'_bound
  have h_from_general := hypercontractive_low_degree f 1 q hq hd h_bb
  have h_rpow_eq : (q - 1) ^ ((↑(1 : ℕ) : ℝ) / 2) = Real.sqrt (q - 1) := by
    rw [Nat.cast_one]
    exact (Real.sqrt_eq_rpow (q - 1)).symm
  rwa [h_rpow_eq] at h_from_general

end BooleanFourier


-- created on 2026-10-23
