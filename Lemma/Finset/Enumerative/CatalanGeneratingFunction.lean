import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped Topology


namespace MetaMathlibExt.CatalanGeneratingFunction

/--
[catalan_le_four_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanGeneratingFunction.lean)
-/
@[path]
private lemma catalan_le_four_pow (n : ℕ) : catalan n ≤ 4 ^ n := by
  rw [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose]
  calc (2 * n).choose n / (n + 1) ≤ (2 * n).choose n := Nat.div_le_self _ _
    _ ≤ 2 ^ (2 * n) := Nat.choose_le_two_pow _ _
    _ = 4 ^ n := by
      have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h4, ← pow_mul]

end MetaMathlibExt.CatalanGeneratingFunction

namespace MetaMathlibExt.CatalanGeneratingFunction

/--
[catalan_summable_norm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanGeneratingFunction.lean)
-/
@[path]
private lemma catalan_summable_norm (t : ℝ) (ht : |t| < 1 / 4) :
  Summable (fun n : ℕ => ‖(catalan n : ℝ) * t ^ n‖) := by
  have hr : 4 * |t| < 1 := by linarith
  have hr0 : (0 : ℝ) ≤ 4 * |t| := by positivity
  refine Summable.of_norm_bounded (summable_geometric_of_lt_one hr0 hr) (fun n => ?_)
  have hc : (0 : ℝ) ≤ (catalan n : ℝ) := by positivity
  have hcat : (catalan n : ℝ) ≤ (4 : ℝ) ^ n := by exact_mod_cast catalan_le_four_pow n
  calc ‖‖(catalan n : ℝ) * t ^ n‖‖ = (catalan n : ℝ) * |t| ^ n := by
    rw [norm_norm, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow,
      abs_of_nonneg hc]
    _ ≤ 4 ^ n * |t| ^ n :=
      mul_le_mul_of_nonneg_right hcat (pow_nonneg (abs_nonneg _) _)
    _ = (4 * |t|) ^ n := (mul_pow _ _ _).symm

end MetaMathlibExt.CatalanGeneratingFunction

namespace MetaMathlibExt.CatalanGeneratingFunction

/--
[catalan_summable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanGeneratingFunction.lean)
-/
@[path]
private lemma catalan_summable (t : ℝ) (ht : |t| < 1 / 4) :
  Summable (fun n : ℕ => (catalan n : ℝ) * t ^ n) :=
  (catalan_summable_norm t ht).of_norm

end MetaMathlibExt.CatalanGeneratingFunction

namespace MetaMathlibExt.CatalanGeneratingFunction

/--
[catalan_fiber_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanGeneratingFunction.lean)
-/
@[path]
private lemma catalan_fiber_eq (t : ℝ) (n : ℕ) :
  (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
    ((catalan kl.1 : ℝ) * t ^ kl.1) * ((catalan kl.2 : ℝ) * t ^ kl.2))
    = (catalan (n + 1) : ℝ) * t ^ n := by
  have hcast : ((catalan (n + 1) : ℕ) : ℝ)
    = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      ((catalan kl.1 : ℝ) * (catalan kl.2 : ℝ)) := by
    rw [catalan_succ', Nat.cast_sum]
    refine Finset.sum_congr rfl (fun kl _ => ?_)
    rw [Nat.cast_mul]
  rw [hcast, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun kl hkl => ?_)
  have hkl2 : kl.1 + kl.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hkl
  have htp : t ^ n = t ^ kl.1 * t ^ kl.2 := by rw [← pow_add, hkl2]
  rw [htp]
  ring

end MetaMathlibExt.CatalanGeneratingFunction

namespace MetaMathlibExt.CatalanGeneratingFunction

/--
[catalan_fun_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanGeneratingFunction.lean)
-/
@[path]
private lemma catalan_fun_eq (t : ℝ) (ht : |t| < 1 / 4) :
  (∑' n : ℕ, (catalan n : ℝ) * t ^ n) =
    1 + t * ((∑' n : ℕ, (catalan n : ℝ) * t ^ n)
      * (∑' n : ℕ, (catalan n : ℝ) * t ^ n)) := by
  have hn := catalan_summable_norm t ht
  have hs := catalan_summable t ht
  have hfib : Summable (fun n : ℕ => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
    ((catalan kl.1 : ℝ) * t ^ kl.1) * ((catalan kl.2 : ℝ) * t ^ kl.2)) :=
    summable_sum_mul_antidiagonal_of_summable_norm'
      (f := fun n : ℕ => (catalan n : ℝ) * t ^ n)
      (g := fun n : ℕ => (catalan n : ℝ) * t ^ n) hn hs hn hs
  have htail : Summable (fun n : ℕ => (catalan (n + 1) : ℝ) * t ^ n) :=
    (summable_congr (fun n => catalan_fiber_eq t n)).mp hfib
  have hSS : (∑' n : ℕ, (catalan n : ℝ) * t ^ n)
    * (∑' n : ℕ, (catalan n : ℝ) * t ^ n)
    = ∑' n : ℕ, (catalan (n + 1) : ℝ) * t ^ n := by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (f := fun n : ℕ => (catalan n : ℝ) * t ^ n)
      (g := fun n : ℕ => (catalan n : ℝ) * t ^ n) hn hn]
    exact tsum_congr (fun n => catalan_fiber_eq t n)
  have htmul : t * ((∑' n : ℕ, (catalan n : ℝ) * t ^ n)
    * (∑' n : ℕ, (catalan n : ℝ) * t ^ n))
    = ∑' n : ℕ, (catalan (n + 1) : ℝ) * t ^ (n + 1) := by
    rw [hSS, ← Summable.tsum_mul_left t htail]
    refine tsum_congr (fun n => ?_)
    rw [pow_succ]
    ring
  have hdecomp : (∑' n : ℕ, (catalan n : ℝ) * t ^ n)
    = 1 + ∑' n : ℕ, (catalan (n + 1) : ℝ) * t ^ (n + 1) := by
    have h := hs.tsum_eq_zero_add
    simp only [catalan_zero, Nat.cast_one, pow_zero, mul_one] at h
    exact h
  rwa [htmul]

end MetaMathlibExt.CatalanGeneratingFunction

namespace MetaMathlibExt.CatalanGeneratingFunction

/--
[catalan_abs_le_of_mem_uIcc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanGeneratingFunction.lean)
-/
@[path]
private lemma catalan_abs_le_of_mem_uIcc {x t : ℝ} (ht : t ∈ Set.uIcc 0 x) : |t| ≤ |x| := by
  rw [Set.mem_uIcc] at ht
  rw [abs_le]
  constructor
  · rcases ht with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact le_trans (neg_nonpos.mpr (abs_nonneg _)) h1
    · exact le_trans (neg_abs_le _) h1
  · rcases ht with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact le_trans h2 (le_abs_self _)
    · exact le_trans h2 (abs_nonneg _)

end MetaMathlibExt.CatalanGeneratingFunction

namespace MetaMathlibExt.CatalanGeneratingFunction

/--
[catalan_continuousOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanGeneratingFunction.lean)
-/
@[path]
private lemma catalan_continuousOn (x : ℝ) (hx : |x| < 1 / 4) :
  ContinuousOn (fun t : ℝ => ∑' n : ℕ, (catalan n : ℝ) * t ^ n) (Set.uIcc 0 x) := by
  have hr : 4 * |x| < 1 := by linarith
  have hr0 : (0 : ℝ) ≤ 4 * |x| := by positivity
  refine continuousOn_tsum (fun n => (continuous_const.mul (continuous_id.pow n)).continuousOn)
    (summable_geometric_of_lt_one hr0 hr) (fun n t ht => ?_)
  have habs : |t| ≤ |x| := catalan_abs_le_of_mem_uIcc ht
  have hc : (0 : ℝ) ≤ (catalan n : ℝ) := by positivity
  have hcat : (catalan n : ℝ) ≤ (4 : ℝ) ^ n := by exact_mod_cast catalan_le_four_pow n
  have hpow : |t| ^ n ≤ |x| ^ n := pow_le_pow_left₀ (abs_nonneg _) habs n
  calc ‖(catalan n : ℝ) * t ^ n‖ = (catalan n : ℝ) * |t| ^ n := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_of_nonneg hc]
    _ ≤ (catalan n : ℝ) * |x| ^ n :=
      mul_le_mul_of_nonneg_left hpow hc
    _ ≤ 4 ^ n * |x| ^ n :=
      mul_le_mul_of_nonneg_right hcat (pow_nonneg (abs_nonneg _) _)
    _ = (4 * |x|) ^ n := (mul_pow _ _ _).symm

end MetaMathlibExt.CatalanGeneratingFunction

namespace MetaMathlibExt.CatalanGeneratingFunction

/--
[catalan_generating_function_sqrt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanGeneratingFunction.lean)
-/
@[path]
lemma catalan_generating_function_sqrt
  {x : ℝ}
-- given
  (hx : |x| < 1 / 4)
  (hx0 : x ≠ 0) :
-- imply
  ∑' n : ℕ, (catalan n : ℝ) * x ^ n =
    (1 - Real.sqrt (1 - 4 * x)) / (2 * x) := by
-- proof
  have hY2 : ∀ t : ℝ, |t| < 1 / 4 →
    (1 - 2 * t * (∑' n : ℕ, (catalan n : ℝ) * t ^ n)) ^ 2 = 1 - 4 * t := by
    intro t ht
    have h := catalan_fun_eq t ht
    have hSq : t * ((∑' n : ℕ, (catalan n : ℝ) * t ^ n)
      * (∑' n : ℕ, (catalan n : ℝ) * t ^ n))
      = (∑' n : ℕ, (catalan n : ℝ) * t ^ n) - 1 := by linarith
    calc (1 - 2 * t * (∑' n : ℕ, (catalan n : ℝ) * t ^ n)) ^ 2
      = 1 - 4 * (t * (∑' n : ℕ, (catalan n : ℝ) * t ^ n))
        + 4 * (t * ((∑' n : ℕ, (catalan n : ℝ) * t ^ n)
          * (∑' n : ℕ, (catalan n : ℝ) * t ^ n))) * t := by
        ring
      _ = 1 - 4 * t := by rw [hSq]; ring
  have hS0 : (∑' n : ℕ, (catalan n : ℝ) * (0 : ℝ) ^ n) = 1 := by
    rw [tsum_eq_single 0]
    · simp [catalan_zero]
    · intro b hb
      rw [zero_pow hb, mul_zero]
  have hScont := catalan_continuousOn x hx
  have hcontY : ContinuousOn
    (fun t : ℝ => 1 - 2 * t * (∑' n : ℕ, (catalan n : ℝ) * t ^ n))
    (Set.uIcc 0 x) :=
    continuousOn_const.sub ((continuousOn_const.mul continuousOn_id).mul hScont)
  have hYpos : 0 < 1 - 2 * x * (∑' n : ℕ, (catalan n : ℝ) * x ^ n) := by
    by_contra hle
    have hle' : 1 - 2 * x * (∑' n : ℕ, (catalan n : ℝ) * x ^ n) ≤ 0 := not_lt.mp hle
    have hY0 : (1 : ℝ) - 2 * 0 * (∑' n : ℕ, (catalan n : ℝ) * (0 : ℝ) ^ n) = 1 := by
      rw [hS0]; ring
    have hmem : (0 : ℝ) ∈ Set.uIcc
      ((fun t : ℝ => 1 - 2 * t * (∑' n : ℕ, (catalan n : ℝ) * t ^ n)) 0)
      ((fun t : ℝ => 1 - 2 * t * (∑' n : ℕ, (catalan n : ℝ) * t ^ n)) x) := by
      rw [Set.mem_uIcc]
      refine Or.inr ⟨hle', ?_⟩
      change (0 : ℝ) ≤ 1 - 2 * 0 * (∑' n : ℕ, (catalan n : ℝ) * (0 : ℝ) ^ n)
      rwa [hY0]
    obtain ⟨t, htmem, ht0⟩ := intermediate_value_uIcc hcontY hmem
    have habs : |t| ≤ |x| := catalan_abs_le_of_mem_uIcc htmem
    have htab : |t| < 1 / 4 := lt_of_le_of_lt habs hx
    have hYt2 := hY2 t htab
    have ht0' : 1 - 2 * t * (∑' n : ℕ, (catalan n : ℝ) * t ^ n) = 0 := ht0
    rw [ht0', zero_pow two_ne_zero] at hYt2
    have hpos : (0 : ℝ) < 1 - 4 * t := by
      have hle2 : t ≤ |t| := le_abs_self _
      linarith
    linarith
  have hYsqrt : 1 - 2 * x * (∑' n : ℕ, (catalan n : ℝ) * x ^ n)
    = Real.sqrt (1 - 4 * x) := by
    have h := hY2 x hx
    rw [← h, Real.sqrt_sq (le_of_lt hYpos)]
  have h2x : (2 : ℝ) * x ≠ 0 := mul_ne_zero two_ne_zero hx0
  rw [eq_div_iff h2x]
  linarith [hYsqrt]
end



-- created on 2026-10-20
-- updated on 2026-10-26
