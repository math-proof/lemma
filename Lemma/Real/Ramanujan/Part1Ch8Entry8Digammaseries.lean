import Mathlib
import sympy.Basic
import Def.Analysis.Ramanujan.Part1Ch8Entry8Digammaseries
open scoped Nat Real BigOperators Interval
open Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch8
open Entry8Digammaseries


namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[chapter8Digamma_eq_Complex_digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
lemma chapter8Digamma_eq_Complex_digamma
  {z : ℂ} :
-- imply
  chapter8Digamma z = Complex.digamma z := by
-- proof
  simp [chapter8Digamma, Complex.digamma_def, logDeriv]

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[bridge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma bridge_iff (f : ℕ → ℂ) (a : ℂ) :
  HasSum f a (SummationFilter.conditional ℕ) ↔
    Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, f i) Filter.atTop (nhds a) := by
  simp only [HasSum, SummationFilter.conditional_filter_eq_map_range]
  rw [Filter.tendsto_map'_iff]
  rfl

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[tendsto_inv_natCast_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma tendsto_inv_natCast_add (c : ℂ) :
  Filter.Tendsto (fun n : ℕ => (((n : ℂ) + c))⁻¹) Filter.atTop (nhds 0) := by
  refine squeeze_zero_norm' (f := fun n : ℕ => (((n : ℂ) + c))⁻¹)
    (a := fun n : ℕ => (((n : ℝ) + (-‖c‖)))⁻¹) ?_ ?_
  · have hev : ∀ᶠ n : ℕ in Filter.atTop, ‖c‖ < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
    filter_upwards [hev] with n hn
    rw [norm_inv]
    have hle : (n : ℝ) + (-‖c‖) ≤ ‖((n : ℂ) + c)‖ := by
      have h := norm_sub_norm_le ((n : ℂ)) (-c)
      rw [Complex.norm_natCast, norm_neg, sub_neg_eq_add] at h
      linarith
    have hpos : (0 : ℝ) < (n : ℝ) + (-‖c‖) := by linarith
    have h := one_div_le_one_div_of_le hpos hle
    rwa [inv_eq_one_div, inv_eq_one_div]
  · have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + (-‖c‖))) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h2 := tendsto_inv_atTop_zero.comp h1
    simpa only [Function.comp_def] using h2

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[pair_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma pair_sum (t : ℕ → ℂ) (N : ℕ) :
  ∑ j ∈ Finset.range (2 * N), t j =
    ∑ k ∈ Finset.range N, (t (2 * k) + t (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e1 : 2 * (N + 1) = (2 * N + 1) + 1 := by ring
    rw [e1, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[merge_even_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma merge_even_odd (S : ℕ → ℂ) (L : ℂ)
  (he : Filter.Tendsto (fun N => S (2 * N)) Filter.atTop (nhds L))
  (ho : Filter.Tendsto (fun N => S (2 * N + 1)) Filter.atTop (nhds L)) :
  Filter.Tendsto S Filter.atTop (nhds L) := by
  rw [Metric.tendsto_atTop] at he ho ⊢
  intro ε hε
  obtain ⟨N1, hN1⟩ := he ε hε
  obtain ⟨N2, hN2⟩ := ho ε hε
  refine ⟨max (2 * N1) (2 * N2 + 1), fun n hn => ?_⟩
  obtain hev | hod := Nat.even_or_odd n
  · obtain ⟨k, hk⟩ := hev
    have hk1 : N1 ≤ k := by omega
    have hnk : n = 2 * k := by omega
    rw [hnk]
    exact hN1 k hk1
  · obtain ⟨k, hk⟩ := hod
    have hk2 : N2 ≤ k := by omega
    rw [hk]
    exact hN2 k hk2

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[term_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma term_even (a b : ℂ) (hb : b ≠ 0)
  (hdenom : ∀ j : ℕ, a + b * ((j + 1 : ℕ) : ℂ) ≠ 0) (k : ℕ) :
  chapter8Entry8Term a b (2 * k) =
    (2 * b)⁻¹ * (((a + b) / (2 * b) + (k : ℂ)))⁻¹ := by
  have h2b : (2 : ℂ) * b ≠ 0 := mul_ne_zero two_ne_zero hb
  have hcast : (((2 * k + 1 : ℕ)) : ℂ) = 2 * (k : ℂ) + 1 := by push_cast; ring
  have hden : a + b * (2 * (k : ℂ) + 1) ≠ 0 := by
    rw [← hcast]; exact hdenom (2 * k)
  have hu : a + b * (2 * (k : ℂ) + 1) = (2 * b) * ((a + b) / (2 * b) + (k : ℂ)) := by
    field_simp
    ring
  have hneg : (-1 : ℂ) ^ (2 * k) = 1 := by rw [pow_mul, neg_one_sq, one_pow]
  simp only [chapter8Entry8Term]
  rw [hcast, hneg, hu, one_div, mul_inv]

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[term_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma term_odd (a b : ℂ) (hb : b ≠ 0)
  (hdenom : ∀ j : ℕ, a + b * ((j + 1 : ℕ) : ℂ) ≠ 0) (k : ℕ) :
  chapter8Entry8Term a b (2 * k + 1) =
    -((2 * b)⁻¹ * (((a + b) / (2 * b) + (k : ℂ) + 1 / 2))⁻¹) := by
  have h2b : (2 : ℂ) * b ≠ 0 := mul_ne_zero two_ne_zero hb
  have hcast : (((2 * k + 1 + 1 : ℕ)) : ℂ) = 2 * (k : ℂ) + 2 := by push_cast; ring
  have hden : a + b * (2 * (k : ℂ) + 2) ≠ 0 := by
    rw [← hcast]; exact hdenom (2 * k + 1)
  have hdenom' : a + b * (2 * (k : ℂ) + 2) ≠ 0 := hden
  have hu : a + b * (2 * (k : ℂ) + 2)
    = (2 * b) * ((a + b) / (2 * b) + (k : ℂ) + 1 / 2) := by
    field_simp
    ring
  have hneg : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
    rw [pow_add, pow_mul, neg_one_sq, one_pow, pow_one, one_mul]
  simp only [chapter8Entry8Term]
  rw [hcast, hneg, neg_div, one_div, hu, mul_inv]

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[u_side](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma u_side (a b : ℂ) (hb : b ≠ 0)
  (hdenom : ∀ j : ℕ, a + b * ((j + 1 : ℕ) : ℂ) ≠ 0) :
  ∀ m : ℕ, (a + b) / (2 * b) ≠ -((m : ℕ) : ℂ) := by
  intro m hm
  have h2b : (2 : ℂ) * b ≠ 0 := mul_ne_zero two_ne_zero hb
  have hcast : (((2 * m + 1 : ℕ)) : ℂ) = 2 * (m : ℂ) + 1 := by push_cast; ring
  have h0 := hdenom (2 * m)
  rw [hcast] at h0
  have heq : a + b * (2 * (m : ℂ) + 1)
    = (2 * b) * (((a + b) / (2 * b)) + (m : ℂ)) := by
    field_simp
    ring
  have hzz : ((-(m : ℂ)) + (m : ℂ)) = 0 := neg_add_cancel _
  rw [hm, hzz, mul_zero] at heq
  exact h0 heq

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[u2_side](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma u2_side (a b : ℂ) (hb : b ≠ 0)
  (hdenom : ∀ j : ℕ, a + b * ((j + 1 : ℕ) : ℂ) ≠ 0) :
  ∀ m : ℕ, ((a + b) / (2 * b) + 1 / 2) ≠ -((m : ℕ) : ℂ) := by
  intro m hm
  have h2b : (2 : ℂ) * b ≠ 0 := mul_ne_zero two_ne_zero hb
  have hcast : (((2 * m + 1 + 1 : ℕ)) : ℂ) = 2 * (m : ℂ) + 2 := by push_cast; ring
  have h0 := hdenom (2 * m + 1)
  rw [hcast] at h0
  have heq : a + b * (2 * (m : ℂ) + 2)
    = (2 * b) * ((((a + b) / (2 * b) + 1 / 2)) + (m : ℂ)) := by
    field_simp
    ring
  have hzz : ((-(m : ℂ)) + (m : ℂ)) = 0 := neg_add_cancel _
  rw [hm, hzz, mul_zero] at heq
  exact h0 heq

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[hv_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma hv_eq (a b : ℂ) (hb : b ≠ 0) :
  (a + 2 * b) / (2 * b) = (a + b) / (2 * b) + 1 / 2 := by
  have h2b : (2 : ℂ) * b ≠ 0 := mul_ne_zero two_ne_zero hb
  field_simp
  ring

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[shift_diff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma shift_diff (u : ℂ) (hu : ∀ m : ℕ, u ≠ -((m : ℕ) : ℂ))
  (hu2 : ∀ m : ℕ, (u + 1 / 2) ≠ -((m : ℕ) : ℂ)) (N : ℕ) :
  ((u + ((N : ℕ) : ℂ)).digamma - u.digamma) -
    (((u + 1 / 2) + ((N : ℕ) : ℂ)).digamma - (u + 1 / 2).digamma)
    = ∑ k ∈ Finset.range N,
      ((u + ((k : ℕ) : ℂ))⁻¹ - (u + ((k : ℕ) : ℂ) + 1 / 2)⁻¹) := by
  rw [Complex.digamma_apply_add_nat hu, Complex.digamma_apply_add_nat hu2,
    add_sub_cancel_left, add_sub_cancel_left, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hkk : ((u + 1 / 2) + ((k : ℕ) : ℂ)) = (u + ((k : ℕ) : ℂ) + 1 / 2) := by ring
  rw [hkk]

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[Seven](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma Seven (a b : ℂ) (hb : b ≠ 0)
  (hdenom : ∀ j : ℕ, a + b * ((j + 1 : ℕ) : ℂ) ≠ 0) (N : ℕ) :
  ∑ j ∈ Finset.range (2 * N), chapter8Entry8Term a b j =
    (2 * b)⁻¹ * (∑ k ∈ Finset.range N,
      ((((a + b) / (2 * b)) + ((k : ℕ) : ℂ))⁻¹ -
        ((((a + b) / (2 * b)) + ((k : ℕ) : ℂ) + 1 / 2))⁻¹)) := by
  rw [pair_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [term_even a b hb hdenom k, term_odd a b hb hdenom k]
  ring

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[ne_neg_nat_of_pos_re](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma ne_neg_nat_of_pos_re (z : ℂ) (hz : 0 < z.re) (m : ℕ) :
  z ≠ -((m : ℕ) : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[halveE](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma halveE (s z : ℂ) (hz : ∀ m : ℕ, z ≠ -((m : ℕ) : ℂ))
  (hzs : ∀ m : ℕ, (z + s) ≠ -((m : ℕ) : ℂ)) :
  Complex.digamma (z + s) - Complex.digamma z =
    1 / 2 * (Complex.digamma (z / 2 + s / 2) - Complex.digamma (z / 2)) +
    1 / 2 * (Complex.digamma (z / 2 + s / 2 + 1 / 2) - Complex.digamma (z / 2 + 1 / 2)) := by
  have hs0 : ∀ m : ℕ, 2 * (z / 2) ≠ -((m : ℕ) : ℂ) := by
    intro m h
    have e : 2 * (z / 2) = z := by ring
    rw [e] at h
    exact hz m h
  have hs1 : ∀ m : ℕ, 2 * ((z + s) / 2) ≠ -((m : ℕ) : ℂ) := by
    intro m h
    have e : 2 * ((z + s) / 2) = z + s := by ring
    rw [e] at h
    exact hzs m h
  have h0 : Complex.digamma z =
    1 / 2 * (Complex.digamma (z / 2) + Complex.digamma (z / 2 + 1 / 2)) +
    Complex.log 2 := by
    have h := Complex.digamma_two_mul (s := z / 2) hs0
    have e : (2 : ℂ) * (z / 2) = z := by ring
    rwa [e] at h
  have h1 : Complex.digamma (z + s) =
    1 / 2 * (Complex.digamma ((z + s) / 2) + Complex.digamma ((z + s) / 2 + 1 / 2)) +
    Complex.log 2 := by
    have h := Complex.digamma_two_mul (s := (z + s) / 2) hs1
    have e : (2 : ℂ) * ((z + s) / 2) = z + s := by ring
    rwa [e] at h
  have e1 : z / 2 + s / 2 = (z + s) / 2 := by ring
  rw [h1, h0, ← e1]
  ring

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[div_two_pow_re](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma div_two_pow_re (z : ℂ) (m : ℕ) : (z / (2 : ℂ) ^ m).re = z.re / (2 ^ m : ℝ) := by
  have e : (2 : ℂ) ^ m = (((2 ^ m : ℝ)) : ℂ) := by push_cast; ring
  rw [e, Complex.div_ofReal_re]

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[avgE](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma avgE (m : ℕ) (w : ℂ) (hw : 0 < w.re) :
  Complex.digamma (w + 1 / 2) - Complex.digamma w =
    (1 / 2) ^ m * ∑ j ∈ Finset.range (2 ^ m),
      (Complex.digamma (w / (2 : ℂ) ^ m + (j : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)) -
        Complex.digamma (w / (2 : ℂ) ^ m + (j : ℂ) / (2 : ℂ) ^ m)) := by
  induction m with
  | zero =>
    have e01 : (0 : ℕ) + 1 = 1 := rfl
    simp only [pow_zero, Finset.sum_range_one, Nat.cast_zero, div_one, one_mul,
      e01, pow_one, add_zero]
  | succ m ih =>
    have h2m : (2 : ℂ) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
    have h2m1 : (2 : ℂ) ^ (m + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
    have h2 : (2 : ℂ) ^ (m + 1) = 2 * (2 : ℂ) ^ m := by rw [pow_succ]; ring
    have hs_eq : (1 / 2 : ℂ) ^ (m + 1) / 2 = (1 / 2 : ℂ) ^ (m + 1 + 1) := by
      rw [pow_succ]; ring
    have hpt_low : ∀ j : ℕ,
      (w / (2 : ℂ) ^ m + (j : ℂ) / (2 : ℂ) ^ m) / 2 =
        w / (2 : ℂ) ^ (m + 1) + (j : ℂ) / (2 : ℂ) ^ (m + 1) := by
      intro j
      rw [h2]
      field_simp
    have hpt_high : ∀ j : ℕ,
      (w / (2 : ℂ) ^ m + (j : ℂ) / (2 : ℂ) ^ m) / 2 + 1 / 2 =
        w / (2 : ℂ) ^ (m + 1) + ((2 ^ m + j : ℕ) : ℂ) / (2 : ℂ) ^ (m + 1) := by
      intro j
      have hj : (((2 ^ m + j : ℕ)) : ℂ) = ((2 ^ m : ℕ) : ℂ) + (j : ℂ) := by
        push_cast; ring
      have h2mn : (((2 ^ m : ℕ)) : ℂ) = (2 : ℂ) ^ m := by push_cast; ring
      rw [h2, hj, h2mn]
      field_simp
      ring
    have hpos : ∀ j ∈ Finset.range (2 ^ m),
      0 < (w / (2 : ℂ) ^ m + (j : ℂ) / (2 : ℂ) ^ m).re := by
      intro j _
      have e : w / (2 : ℂ) ^ m + (j : ℂ) / (2 : ℂ) ^ m = (w + (j : ℂ)) / (2 : ℂ) ^ m := by
        rw [← add_div]
      rw [e, div_two_pow_re]
      have hjnn : (0 : ℝ) ≤ ((j : ℂ)).re := by
        rw [Complex.natCast_re]
        exact Nat.cast_nonneg j
      have h2pos : (0 : ℝ) < (2 ^ m : ℝ) := by positivity
      have hwr : (0 : ℝ) < (w + (j : ℂ)).re := by
        rw [Complex.add_re]
        linarith
      exact div_pos hwr h2pos
    have hpos2 : ∀ j ∈ Finset.range (2 ^ m),
      0 < (w / (2 : ℂ) ^ m + (j : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)).re := by
      intro j hj
      have hsnn : (0 : ℝ) ≤ ((1 / 2 : ℂ) ^ (m + 1)).re := by
        have e : (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) := by norm_num
        rw [e, ← Complex.ofReal_pow, Complex.ofReal_re]
        positivity
      rw [Complex.add_re]
      have := hpos j hj
      linarith
    have hsplit : ∀ j ∈ Finset.range (2 ^ m),
      (Complex.digamma (w / (2 : ℂ) ^ m + (j : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)) -
        Complex.digamma (w / (2 : ℂ) ^ m + (j : ℂ) / (2 : ℂ) ^ m)) =
      1 / 2 * (Complex.digamma (w / (2 : ℂ) ^ (m + 1) + (j : ℂ) / (2 : ℂ) ^ (m + 1) +
        (1 / 2 : ℂ) ^ (m + 1 + 1)) -
        Complex.digamma (w / (2 : ℂ) ^ (m + 1) + (j : ℂ) / (2 : ℂ) ^ (m + 1))) +
      1 / 2 * (Complex.digamma (w / (2 : ℂ) ^ (m + 1) +
        ((2 ^ m + j : ℕ) : ℂ) / (2 : ℂ) ^ (m + 1) + (1 / 2 : ℂ) ^ (m + 1 + 1)) -
        Complex.digamma (w / (2 : ℂ) ^ (m + 1) +
          ((2 ^ m + j : ℕ) : ℂ) / (2 : ℂ) ^ (m + 1))) := by
      intro j hj
      have hz : ∀ k : ℕ, (w / (2 : ℂ) ^ m + (j : ℂ) / (2 : ℂ) ^ m) ≠ -((k : ℕ) : ℂ) :=
        fun k => ne_neg_nat_of_pos_re _ (hpos j hj) k
      have hzs : ∀ k : ℕ, (w / (2 : ℂ) ^ m + (j : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)) ≠
        -((k : ℕ) : ℂ) :=
        fun k => ne_neg_nat_of_pos_re _ (hpos2 j hj) k
      have h := halveE ((1 / 2 : ℂ) ^ (m + 1)) (w / (2 : ℂ) ^ m + (j : ℂ) / (2 : ℂ) ^ m) hz hzs
      rw [hs_eq, hpt_low j] at h
      have hlow_high : (w / (2 : ℂ) ^ (m + 1) + (j : ℂ) / (2 : ℂ) ^ (m + 1)) + 1 / 2 =
        w / (2 : ℂ) ^ (m + 1) + ((2 ^ m + j : ℕ) : ℂ) / (2 : ℂ) ^ (m + 1) := by
        have hh := hpt_high j
        rwa [hpt_low j] at hh
      have e5 : (w / (2 : ℂ) ^ (m + 1) + (j : ℂ) / (2 : ℂ) ^ (m + 1) +
        (1 / 2 : ℂ) ^ (m + 1 + 1)) + 1 / 2 =
        ((w / (2 : ℂ) ^ (m + 1) + (j : ℂ) / (2 : ℂ) ^ (m + 1)) + 1 / 2) +
          (1 / 2 : ℂ) ^ (m + 1 + 1) := by ring
      rwa [e5, hlow_high] at h
    have hsum : ∑ j ∈ Finset.range (2 ^ m),
      (Complex.digamma (w / (2 : ℂ) ^ m + (j : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)) -
        Complex.digamma (w / (2 : ℂ) ^ m + (j : ℂ) / (2 : ℂ) ^ m)) =
      ∑ j ∈ Finset.range (2 ^ m),
        (1 / 2 * (Complex.digamma (w / (2 : ℂ) ^ (m + 1) + (j : ℂ) / (2 : ℂ) ^ (m + 1) +
          (1 / 2 : ℂ) ^ (m + 1 + 1)) -
          Complex.digamma (w / (2 : ℂ) ^ (m + 1) + (j : ℂ) / (2 : ℂ) ^ (m + 1))) +
        1 / 2 * (Complex.digamma (w / (2 : ℂ) ^ (m + 1) +
          ((2 ^ m + j : ℕ) : ℂ) / (2 : ℂ) ^ (m + 1) + (1 / 2 : ℂ) ^ (m + 1 + 1)) -
          Complex.digamma (w / (2 : ℂ) ^ (m + 1) +
            ((2 ^ m + j : ℕ) : ℂ) / (2 : ℂ) ^ (m + 1)))) :=
      Finset.sum_congr rfl (fun j hj => hsplit j hj)
    have e2m : 2 ^ m + 2 ^ m = 2 ^ (m + 1) := by ring
    have hcomb : ∑ j ∈ Finset.range (2 ^ m),
      (Complex.digamma (w / (2 : ℂ) ^ (m + 1) + (j : ℂ) / (2 : ℂ) ^ (m + 1) +
        (1 / 2 : ℂ) ^ (m + 1 + 1)) -
        Complex.digamma (w / (2 : ℂ) ^ (m + 1) + (j : ℂ) / (2 : ℂ) ^ (m + 1))) +
      ∑ j ∈ Finset.range (2 ^ m),
        (Complex.digamma (w / (2 : ℂ) ^ (m + 1) +
          ((2 ^ m + j : ℕ) : ℂ) / (2 : ℂ) ^ (m + 1) + (1 / 2 : ℂ) ^ (m + 1 + 1)) -
          Complex.digamma (w / (2 : ℂ) ^ (m + 1) +
            ((2 ^ m + j : ℕ) : ℂ) / (2 : ℂ) ^ (m + 1))) =
      ∑ j ∈ Finset.range (2 ^ (m + 1)),
        (Complex.digamma (w / (2 : ℂ) ^ (m + 1) + (j : ℂ) / (2 : ℂ) ^ (m + 1) +
          (1 / 2 : ℂ) ^ (m + 1 + 1)) -
          Complex.digamma (w / (2 : ℂ) ^ (m + 1) + (j : ℂ) / (2 : ℂ) ^ (m + 1))) := by
      rw [← e2m]
      rw [Finset.sum_range_add]
    rw [ih, hsum, Finset.sum_add_distrib, mul_add, ← Finset.mul_sum, ← Finset.mul_sum,
      ← mul_assoc, ← mul_assoc, ← pow_succ, ← mul_add, hcomb]

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[ball_re](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma ball_re (z : ℂ) (hz : z ∈ Metric.closedBall 2 (3 / 2 : ℝ)) :
  1 / 2 ≤ z.re ∧ z.re ≤ 7 / 2 := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h2 : (z - 2).re = z.re - 2 := by simp [Complex.sub_re]
  have h1 : |z.re - 2| ≤ ‖z - 2‖ := by
    rw [← h2]
    exact Complex.abs_re_le_norm _
  have h : |z.re - 2| ≤ 3 / 2 := le_trans h1 hz
  constructor <;> linarith [abs_le.mp h]

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[ball_polefree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma ball_polefree (z : ℂ) (hz : z ∈ Metric.closedBall 2 (3 / 2 : ℝ)) (m : ℕ) :
  z ≠ -((m : ℕ) : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  obtain ⟨h1, h2⟩ := ball_re z hz
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[digamma_contOn_ball](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma digamma_contOn_ball :
  ContinuousOn Complex.digamma (Metric.closedBall 2 (3 / 2 : ℝ)) := by
  intro z hz
  exact (Complex.analyticAt_digamma z (ball_polefree z hz)).differentiableAt.continuousAt.continuousWithinAt

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[digamma_modulus](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma digamma_modulus (ε : ℝ) (hε : 0 < ε) :
  ∃ δ > 0, ∀ z ∈ Metric.closedBall 2 (3 / 2 : ℝ), ∀ z' ∈ Metric.closedBall 2 (3 / 2 : ℝ),
    dist z z' < δ → dist (Complex.digamma z) (Complex.digamma z') < ε := by
  have hC : IsCompact (Metric.closedBall (2 : ℂ) (3 / 2 : ℝ)) :=
    ProperSpace.isCompact_closedBall _ _
  have hU : UniformContinuousOn Complex.digamma (Metric.closedBall 2 (3 / 2 : ℝ)) :=
    IsCompact.uniformContinuousOn_of_continuous hC digamma_contOn_ball
  exact Metric.uniformContinuousOn_iff.mp hU ε hε

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[gapE](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma gapE (w : ℂ) (hw : ∀ m : ℕ, w ≠ -((m : ℕ) : ℂ))
  (hw2 : ∀ m : ℕ, (w + 1 / 2) ≠ -((m : ℕ) : ℂ)) (J : ℕ) :
  (Complex.digamma (w + 1 / 2) - Complex.digamma w) -
    (Complex.digamma (w + ((J : ℕ) : ℂ) + 1 / 2) - Complex.digamma (w + ((J : ℕ) : ℂ))) =
  ∑ k ∈ Finset.range J,
    ((w + ((k : ℕ) : ℂ))⁻¹ - (w + 1 / 2 + ((k : ℕ) : ℂ))⁻¹) := by
  have h1 := Complex.digamma_apply_add_nat hw J
  have h2 := Complex.digamma_apply_add_nat hw2 J
  have e1 : w + ((J : ℕ) : ℂ) + 1 / 2 = (w + 1 / 2) + ((J : ℕ) : ℂ) := by ring
  rw [e1, h1, h2, Finset.sum_sub_distrib]
  ring

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[div_two_pow_im](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma div_two_pow_im (z : ℂ) (m : ℕ) :
  (z / (2 : ℂ) ^ m).im = z.im / (2 ^ m : ℝ) := by
  have e : (2 : ℂ) ^ m = (((2 ^ m : ℝ)) : ℂ) := by push_cast; ring
  rw [e, Complex.div_ofReal_im]

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[ball_mem_of_re_im](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma ball_mem_of_re_im (z : ℂ) (h1 : 1 ≤ z.re) (h2 : z.re ≤ 3)
  (him : |z.im| ≤ 1) : z ∈ Metric.closedBall 2 (3 / 2 : ℝ) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hre : (z - 2).re = z.re - 2 := by
    simp only [Complex.sub_re, Complex.re_ofNat]
  have him2 : (z - 2).im = z.im := by
    simp only [Complex.sub_im, Complex.im_ofNat, sub_zero]
  have habs1 : |(z - 2).re| ≤ 1 := by
    rw [hre]
    rw [abs_le]
    constructor <;> linarith
  have habs2 : |(z - 2).im| ≤ 1 := by rw [him2]; exact him
  have hsq1 : (z - 2).re ^ 2 ≤ 1 := by
    rwa [sq_le_one_iff_abs_le_one]
  have hsq2 : (z - 2).im ^ 2 ≤ 1 := by
    rwa [sq_le_one_iff_abs_le_one]
  rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sqrt_le_iff]
  constructor
  · norm_num
  · have hsum : (z - 2).re ^ 2 + (z - 2).im ^ 2 ≤ 2 := by linarith
    have h23 : (2 : ℝ) ≤ (3 / 2) ^ 2 := by norm_num
    linarith

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[exists_scale](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma exists_scale (R : ℝ) (hR : 1 ≤ R) :
  ∃ m : ℕ, 1 ≤ R / (2 ^ m : ℝ) ∧ R / (2 ^ m : ℝ) < 2 := by
  classical
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R (by norm_num : (1 : ℝ) < 2)
  have hex : ∃ m : ℕ, R < (2 : ℝ) ^ (m + 1) := ⟨n, lt_of_lt_of_le hn (by
    have h2 : (1 : ℝ) ≤ 2 := by norm_num
    calc (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + 1) := by
      apply pow_le_pow_right₀ h2 (Nat.le_succ n)
      _ = (2 : ℝ) ^ (n + 1) := rfl)⟩
  refine ⟨Nat.find hex, ?_, ?_⟩
  · have h2m : (0 : ℝ) < (2 : ℝ) ^ (Nat.find hex) := by positivity
    rw [le_div_iff₀ h2m]
    by_contra hcon
    simp only [not_le] at hcon
    have hlt2 : R < (2 : ℝ) ^ (Nat.find hex) := by linarith
    cases Nat.eq_zero_or_pos (Nat.find hex) with
    | inl hz =>
      rw [hz] at hlt2
      simp only [pow_zero] at hlt2
      linarith
    | inr hpos =>
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
      have hkm : k < Nat.find hex := by omega
      have hkneg := Nat.find_min hex hkm
      rw [hk] at hlt2
      exact hkneg hlt2
  · have hmin : R < (2 : ℝ) ^ (Nat.find hex + 1) := Nat.find_spec hex
    have h2m : (0 : ℝ) < (2 : ℝ) ^ (Nat.find hex) := by positivity
    have hpow : (2 : ℝ) ^ (Nat.find hex + 1) = 2 * (2 : ℝ) ^ (Nat.find hex) := by
      rw [pow_succ, mul_comm]
    rw [hpow] at hmin
    rw [div_lt_iff₀ h2m]
    linarith

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[tail_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma tail_tendsto (a b : ℂ) (hb : b ≠ 0)
  (hdenom : ∀ j : ℕ, a + b * ((j + 1 : ℕ) : ℂ) ≠ 0) :
  Filter.Tendsto
    (fun N : ℕ => ((((a + b) / (2 * b) + 1 / 2) + ((N : ℕ) : ℂ)).digamma -
      ((((a + b) / (2 * b))) + ((N : ℕ) : ℂ)).digamma))
    Filter.atTop (nhds 0) := by
  have _hb := hb
  have _hdenom := hdenom
  set u : ℂ := (a + b) / (2 * b) with hu_def
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδpos, hδmod⟩ := digamma_modulus ε hε
  obtain ⟨N1, hN1⟩ := exists_nat_ge (1 - u.re)
  obtain ⟨N2, hN2⟩ := exists_nat_ge ((1 / δ) - u.re)
  obtain ⟨N3, hN3⟩ := exists_nat_ge ((2 * |u.im|) - u.re)
  refine ⟨max N1 (max N2 N3), fun N hN => ?_⟩
  have hN1' : N1 ≤ N := le_trans (le_max_left _ _) hN
  have hN2' : N2 ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN3' : N3 ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have cN1 : (N1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1'
  have cN2 : (N2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2'
  have cN3 : (N3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3'
  have hR1 : (1 : ℝ) ≤ u.re + (N : ℝ) := by linarith
  have hR2 : (1 / δ) ≤ u.re + (N : ℝ) := by linarith
  have hR3 : (2 * |u.im|) ≤ u.re + (N : ℝ) := by linarith
  have hR_eq : (u + ((N : ℕ) : ℂ)).re = u.re + (N : ℝ) := by
    simp only [Complex.add_re, Complex.natCast_re]
  have hI_eq : (u + ((N : ℕ) : ℂ)).im = u.im := by
    simp only [Complex.add_im, Complex.natCast_im, add_zero]
  have hwpos : 0 < (u + ((N : ℕ) : ℂ)).re := by linarith [hR_eq ▸ hR1]
  obtain ⟨m, hm1, hm2⟩ := exists_scale _ (hR_eq ▸ hR1)
  have havg := avgE m (u + ((N : ℕ) : ℂ)) hwpos
  have e_w : (u + 1 / 2) + ((N : ℕ) : ℂ) = (u + ((N : ℕ) : ℂ)) + 1 / 2 := by
    ring
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have h2ne : (2 : ℝ) ^ m ≠ 0 := ne_of_gt h2pos
  have hP_eq : (((2 ^ m : ℕ)) : ℝ) = (2 : ℝ) ^ m := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  have h12_eq : (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) := by norm_num
  have h_half_re : ((1 / 2 : ℂ) ^ (m + 1)).re = (1 / 2 : ℝ) ^ (m + 1) := by
    rw [h12_eq, ← Complex.ofReal_pow, Complex.ofReal_re]
  have h_half_im : ((1 / 2 : ℂ) ^ (m + 1)).im = 0 := by
    rw [h12_eq, ← Complex.ofReal_pow, Complex.ofReal_im]
  have h12_norm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    rw [h12_eq, Complex.norm_of_nonneg (by norm_num)]
  have h_half_pow_norm : ‖(1 / 2 : ℂ) ^ (m + 1)‖ = (1 / 2 : ℝ) ^ (m + 1) := by
    rw [Complex.norm_pow, h12_norm]
  have h_half_m_norm : ‖(1 / 2 : ℂ) ^ m‖ = (1 / 2 : ℝ) ^ m := by
    rw [Complex.norm_pow, h12_norm]
  have h_half_eq : (1 / 2 : ℝ) ^ (m + 1) = 1 / (2 : ℝ) ^ (m + 1) := by
    rw [div_pow, one_pow]
  have hδ0 : (0 : ℝ) < δ := hδpos
  have h2m1_pos : (0 : ℝ) < (2 : ℝ) ^ (m + 1) := by positivity
  have hR_lt_pow : u.re + (N : ℝ) < (2 : ℝ) ^ (m + 1) := by
    have hdiv : (u.re + (N : ℝ)) / (2 : ℝ) ^ m < 2 := by
      have heq : (u + ((N : ℕ) : ℂ)).re / (2 : ℝ) ^ m < 2 := hm2
      rwa [hR_eq] at heq
    have hlt : u.re + (N : ℝ) < 2 * (2 : ℝ) ^ m := by
      rwa [div_lt_iff₀ h2pos] at hdiv
    have hpow : (2 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ m := by
      rw [pow_succ, mul_comm]
    rwa [hpow]
  have h_small : ‖(1 / 2 : ℂ) ^ (m + 1)‖ < δ := by
    rw [h_half_pow_norm, h_half_eq]
    have h1d : (1 : ℝ) / δ < (2 : ℝ) ^ (m + 1) := lt_of_le_of_lt hR2 hR_lt_pow
    have h_one_lt : (1 : ℝ) < δ * (2 : ℝ) ^ (m + 1) := by
      have hiff := (div_lt_iff₀ hδ0).mp h1d
      linarith
    have hiff2 : (1 : ℝ) / (2 : ℝ) ^ (m + 1) < δ :=
      (div_lt_iff₀ h2m1_pos).mpr (by linarith)
    exact hiff2
  have h_im_le : |u.im| ≤ (2 : ℝ) ^ m := by
    have hlt : 2 * |u.im| < 2 * (2 : ℝ) ^ m := by
      have hpow : (2 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ m := by
        rw [pow_succ, mul_comm]
      have h2 : (2 : ℝ) * |u.im| < (2 : ℝ) ^ (m + 1) :=
        lt_of_le_of_lt hR3 hR_lt_pow
      rwa [hpow] at h2
    have h : |u.im| < (2 : ℝ) ^ m := by linarith
    exact le_of_lt h
  have hm1' : (1 : ℝ) ≤ (u.re + (N : ℝ)) / (2 : ℝ) ^ m := by
    have heq := hm1
    rwa [hR_eq] at heq
  have hm2' : (u.re + (N : ℝ)) / (2 : ℝ) ^ m < 2 := by
    have heq := hm2
    rwa [hR_eq] at heq
  have h_each : ∀ j ∈ Finset.range (2 ^ m),
    ‖Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m + ((j : ℕ) : ℂ) /
      (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)) -
      Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
        ((j : ℕ) : ℂ) / (2 : ℂ) ^ m)‖ < ε := by
    intro j hj
    have hj_mem : j < 2 ^ m := Finset.mem_range.mp hj
    have hj_nn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hj_lt : (j : ℝ) < (2 : ℝ) ^ m := by
      have hlt_nat : j < 2 ^ m := hj_mem
      have hcast : (j : ℝ) < (((2 ^ m : ℕ)) : ℝ) := by exact_mod_cast hlt_nat
      rwa [hP_eq] at hcast
    have hj_le : (j : ℝ) ≤ (2 : ℝ) ^ m - 1 := by
      have hsucc : j + 1 ≤ 2 ^ m := Nat.succ_le_of_lt hj_mem
      have hcast : ((j + 1 : ℕ) : ℝ) ≤ (((2 ^ m : ℕ)) : ℝ) := by
        exact_mod_cast hsucc
      rw [Nat.cast_add, Nat.cast_one, hP_eq] at hcast
      linarith
    have hz_re : ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m + ((j : ℕ) : ℂ) /
      (2 : ℂ) ^ m).re = (u.re + (N : ℝ)) / (2 : ℝ) ^ m + (j : ℝ) /
      (2 : ℝ) ^ m := by
      rw [Complex.add_re, div_two_pow_re, div_two_pow_re, hR_eq]
      simp only [Complex.natCast_re]
    have hz_im : ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m + ((j : ℕ) : ℂ) /
      (2 : ℂ) ^ m).im = u.im / (2 : ℝ) ^ m := by
      rw [Complex.add_im, div_two_pow_im, div_two_pow_im, hI_eq]
      simp only [Complex.natCast_im, zero_div, add_zero]
    have hzs_re : ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m + ((j : ℕ) : ℂ) /
      (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)).re =
      (u.re + (N : ℝ)) / (2 : ℝ) ^ m + (j : ℝ) / (2 : ℝ) ^ m +
      (1 / 2 : ℝ) ^ (m + 1) := by
      rw [Complex.add_re, hz_re, h_half_re]
    have hzs_im : ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m + ((j : ℕ) : ℂ) /
      (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)).im = u.im / (2 : ℝ) ^ m := by
      rw [Complex.add_im, hz_im, h_half_im, add_zero]
    have hj_div_nn : (0 : ℝ) ≤ (j : ℝ) / (2 : ℝ) ^ m :=
      div_nonneg hj_nn h2pos.le
    have hj_div_lt1 : (j : ℝ) / (2 : ℝ) ^ m < 1 :=
      (div_lt_one h2pos).mpr hj_lt
    have hj_div_le1 : (j : ℝ) / (2 : ℝ) ^ m ≤ 1 := le_of_lt hj_div_lt1
    have hs_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (m + 1) := by positivity
    have hpow_succ : (2 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ m := by
      rw [pow_succ, mul_comm]
    have hs_eq : (1 / 2 : ℝ) ^ (m + 1) = 1 / (2 * (2 : ℝ) ^ m) := by
      rw [h_half_eq, hpow_succ]
    have hj_s_le1 : (j : ℝ) / (2 : ℝ) ^ m + (1 / 2 : ℝ) ^ (m + 1) ≤ 1 := by
      rw [hs_eq]
      have hle : (j : ℝ) + 1 / 2 ≤ (2 : ℝ) ^ m := by linarith
      have h_eq : (j : ℝ) / (2 : ℝ) ^ m + 1 / (2 * (2 : ℝ) ^ m) =
        ((j : ℝ) + 1 / 2) / (2 : ℝ) ^ m := by
        field_simp
      rwa [h_eq, div_le_one h2pos]
    have hz_ge1 : (1 : ℝ) ≤ ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
      ((j : ℕ) : ℂ) / (2 : ℂ) ^ m).re := by
      rw [hz_re]
      linarith
    have hz_le3 : ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
      ((j : ℕ) : ℂ) / (2 : ℂ) ^ m).re ≤ 3 := by
      rw [hz_re]
      linarith
    have hzs_ge1 : (1 : ℝ) ≤ ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
      ((j : ℕ) : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)).re := by
      rw [hzs_re]
      linarith
    have hzs_le3 : ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
      ((j : ℕ) : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)).re ≤ 3 := by
      rw [hzs_re]
      linarith [hj_s_le1, hm2']
    have hz_im_abs : |((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
      ((j : ℕ) : ℂ) / (2 : ℂ) ^ m).im| ≤ 1 := by
      rwa [hz_im, abs_div, abs_of_pos h2pos, div_le_one h2pos]
    have hzs_im_abs : |((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
      ((j : ℕ) : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)).im| ≤ 1 := by
      rwa [hzs_im, abs_div, abs_of_pos h2pos, div_le_one h2pos]
    have hz_mem := ball_mem_of_re_im _ hz_ge1 hz_le3 hz_im_abs
    have hzs_mem := ball_mem_of_re_im _ hzs_ge1 hzs_le3 hzs_im_abs
    have h_dist : dist ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
      ((j : ℕ) : ℂ) / (2 : ℂ) ^ m) ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
      ((j : ℕ) : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)) < δ := by
      have e : ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m + ((j : ℕ) : ℂ) /
        (2 : ℂ) ^ m) - ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
        ((j : ℕ) : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)) =
        -((1 / 2 : ℂ) ^ (m + 1)) := by ring
      rwa [dist_eq_norm, e, norm_neg]
    have h_dist' : dist ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
      ((j : ℕ) : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1))
      ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
        ((j : ℕ) : ℂ) / (2 : ℂ) ^ m) < δ := by
      rwa [dist_comm]
    have h_mod := hδmod _ hzs_mem _ hz_mem h_dist'
    rwa [dist_eq_norm] at h_mod
  have hDN_eq : Complex.digamma ((u + 1 / 2) + ((N : ℕ) : ℂ)) -
    Complex.digamma (u + ((N : ℕ) : ℂ)) = (1 / 2 : ℂ) ^ m *
    ∑ j ∈ Finset.range (2 ^ m),
      (Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
        ((j : ℕ) : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)) -
        Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
          ((j : ℕ) : ℂ) / (2 : ℂ) ^ m)) := by
    rwa [e_w]
  have h_goal_rw : dist (Complex.digamma ((u + 1 / 2) + ((N : ℕ) : ℂ)) -
    Complex.digamma (u + ((N : ℕ) : ℂ))) 0 =
    ‖(1 / 2 : ℂ) ^ m * ∑ j ∈ Finset.range (2 ^ m),
      (Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
        ((j : ℕ) : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)) -
        Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
          ((j : ℕ) : ℂ) / (2 : ℂ) ^ m))‖ := by
    rw [dist_eq_norm, sub_zero, hDN_eq]
  rw [h_goal_rw, norm_mul, h_half_m_norm]
  have h_sum_le : ‖∑ j ∈ Finset.range (2 ^ m),
    (Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
      ((j : ℕ) : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)) -
      Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
        ((j : ℕ) : ℂ) / (2 : ℂ) ^ m))‖ ≤
    ∑ j ∈ Finset.range (2 ^ m),
      ‖Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
        ((j : ℕ) : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)) -
        Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
          ((j : ℕ) : ℂ) / (2 : ℂ) ^ m)‖ :=
    norm_sum_le _ _
  have h_ne : (Finset.range (2 ^ m)).Nonempty :=
    ⟨0, Finset.mem_range.mpr (by positivity)⟩
  have h_sum_lt : ∑ j ∈ Finset.range (2 ^ m),
    ‖Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
      ((j : ℕ) : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)) -
      Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
        ((j : ℕ) : ℂ) / (2 : ℂ) ^ m)‖ <
    ∑ _j ∈ Finset.range (2 ^ m), ε :=
    Finset.sum_lt_sum_of_nonempty h_ne h_each
  have h_sum_const : ∑ _j ∈ Finset.range (2 ^ m), ε = (2 : ℝ) ^ m * ε := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hP_eq]
  have h_sum_lt2 : ∑ j ∈ Finset.range (2 ^ m),
    ‖Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
      ((j : ℕ) : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)) -
      Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
        ((j : ℕ) : ℂ) / (2 : ℂ) ^ m)‖ < (2 : ℝ) ^ m * ε := by
    rwa [h_sum_const] at h_sum_lt
  have h_half_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ m := by positivity
  have h_pow_eq : (1 / 2 : ℝ) ^ m * (2 : ℝ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  have h1 : (1 / 2 : ℝ) ^ m * ‖∑ j ∈ Finset.range (2 ^ m),
    (Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
      ((j : ℕ) : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)) -
      Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
        ((j : ℕ) : ℂ) / (2 : ℂ) ^ m))‖ ≤
    (1 / 2 : ℝ) ^ m * ∑ j ∈ Finset.range (2 ^ m),
      ‖Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
        ((j : ℕ) : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)) -
        Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
          ((j : ℕ) : ℂ) / (2 : ℂ) ^ m)‖ :=
    mul_le_mul_of_nonneg_left h_sum_le (le_of_lt h_half_pos)
  have h2 : (1 / 2 : ℝ) ^ m * ∑ j ∈ Finset.range (2 ^ m),
    ‖Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
      ((j : ℕ) : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)) -
      Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
        ((j : ℕ) : ℂ) / (2 : ℂ) ^ m)‖ <
    (1 / 2 : ℝ) ^ m * ((2 : ℝ) ^ m * ε) :=
    mul_lt_mul_of_pos_left h_sum_lt2 h_half_pos
  have h3 : (1 / 2 : ℝ) ^ m * ((2 : ℝ) ^ m * ε) = ε := by
    rw [← mul_assoc, h_pow_eq, one_mul]
  calc (1 / 2 : ℝ) ^ m * ‖∑ j ∈ Finset.range (2 ^ m),
    (Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
      ((j : ℕ) : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)) -
      Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
        ((j : ℕ) : ℂ) / (2 : ℂ) ^ m))‖
    ≤ (1 / 2 : ℝ) ^ m * ∑ j ∈ Finset.range (2 ^ m),
      ‖Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
        ((j : ℕ) : ℂ) / (2 : ℂ) ^ m + (1 / 2 : ℂ) ^ (m + 1)) -
        Complex.digamma ((u + ((N : ℕ) : ℂ)) / (2 : ℂ) ^ m +
          ((j : ℕ) : ℂ) / (2 : ℂ) ^ m)‖ := h1
    _ < (1 / 2 : ℝ) ^ m * ((2 : ℝ) ^ m * ε) := h2
    _ = ε := h3

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[Seven_limit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma Seven_limit (a b : ℂ) (hb : b ≠ 0)
  (hdenom : ∀ j : ℕ, a + b * ((j + 1 : ℕ) : ℂ) ≠ 0)
  (htail : Filter.Tendsto
    (fun N : ℕ => ((((a + b) / (2 * b) + 1 / 2) + ((N : ℕ) : ℂ)).digamma -
      ((((a + b) / (2 * b))) + ((N : ℕ) : ℂ)).digamma))
    Filter.atTop (nhds 0)) :
  Filter.Tendsto (fun N => ∑ j ∈ Finset.range (2 * N), chapter8Entry8Term a b j)
    Filter.atTop
      (nhds (((((a + b) / (2 * b) + 1 / 2).digamma - ((a + b) / (2 * b)).digamma)) *
        (2 * b)⁻¹)) := by
  have hu := u_side a b hb hdenom
  have hu2 := u2_side a b hb hdenom
  have key : ∀ N : ℕ, (∑ j ∈ Finset.range (2 * N), chapter8Entry8Term a b j)
    = ((((a + b) / (2 * b) + 1 / 2).digamma - ((a + b) / (2 * b)).digamma)) * (2 * b)⁻¹
      - ((((a + b) / (2 * b) + 1 / 2) + ((N : ℕ) : ℂ)).digamma -
        ((((a + b) / (2 * b))) + ((N : ℕ) : ℂ)).digamma) * (2 * b)⁻¹ := by
    intro N
    rw [Seven a b hb hdenom N, ← shift_diff ((a + b) / (2 * b)) hu hu2 N]
    ring
  have h2 : Filter.Tendsto
    (fun N : ℕ => ((((a + b) / (2 * b) + 1 / 2) + ((N : ℕ) : ℂ)).digamma -
      ((((a + b) / (2 * b))) + ((N : ℕ) : ℂ)).digamma) * (2 * b)⁻¹)
    Filter.atTop (nhds (0 * (2 * b)⁻¹)) :=
    htail.mul tendsto_const_nhds
  rw [zero_mul] at h2
  have h3 : Filter.Tendsto
    (fun N : ℕ => ((((a + b) / (2 * b) + 1 / 2).digamma -
      ((a + b) / (2 * b)).digamma)) * (2 * b)⁻¹
      - ((((a + b) / (2 * b) + 1 / 2) + ((N : ℕ) : ℂ)).digamma -
        ((((a + b) / (2 * b))) + ((N : ℕ) : ℂ)).digamma) * (2 * b)⁻¹)
    Filter.atTop
      (nhds (((((a + b) / (2 * b) + 1 / 2).digamma -
        ((a + b) / (2 * b)).digamma)) * (2 * b)⁻¹ - 0)) :=
    tendsto_const_nhds.sub h2
  rw [sub_zero] at h3
  have h4 : (fun N => ∑ j ∈ Finset.range (2 * N), chapter8Entry8Term a b j)
    = (fun N : ℕ => ((((a + b) / (2 * b) + 1 / 2).digamma -
      ((a + b) / (2 * b)).digamma)) * (2 * b)⁻¹
      - ((((a + b) / (2 * b) + 1 / 2) + ((N : ℕ) : ℂ)).digamma -
        ((((a + b) / (2 * b))) + ((N : ℕ) : ℂ)).digamma) * (2 * b)⁻¹) :=
    funext (fun N => key N)
  rwa [h4]

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[Sodd_limit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
private lemma Sodd_limit (a b : ℂ) (hb : b ≠ 0)
  (hdenom : ∀ j : ℕ, a + b * ((j + 1 : ℕ) : ℂ) ≠ 0)
  (heven : Filter.Tendsto (fun N => ∑ j ∈ Finset.range (2 * N), chapter8Entry8Term a b j)
    Filter.atTop
      (nhds (((((a + b) / (2 * b) + 1 / 2).digamma - ((a + b) / (2 * b)).digamma)) *
        (2 * b)⁻¹))) :
  Filter.Tendsto (fun N => ∑ j ∈ Finset.range (2 * N + 1), chapter8Entry8Term a b j)
    Filter.atTop
      (nhds (((((a + b) / (2 * b) + 1 / 2).digamma - ((a + b) / (2 * b)).digamma)) *
        (2 * b)⁻¹)) := by
  have hodd_term : Filter.Tendsto (fun N : ℕ => chapter8Entry8Term a b (2 * N))
    Filter.atTop (nhds 0) := by
    have e : (fun N : ℕ => chapter8Entry8Term a b (2 * N))
      = (fun N : ℕ => (2 * b)⁻¹ * ((((a + b) / (2 * b)) + ((N : ℕ) : ℂ))⁻¹)) :=
      funext (fun N => term_even a b hb hdenom N)
    rw [e]
    have h0 : Filter.Tendsto (fun N : ℕ => ((((a + b) / (2 * b)) + ((N : ℕ) : ℂ))⁻¹))
      Filter.atTop (nhds 0) := by
      have e2 : (fun N : ℕ => ((((a + b) / (2 * b)) + ((N : ℕ) : ℂ))⁻¹))
        = (fun N : ℕ => (((((N : ℕ) : ℂ) + ((a + b) / (2 * b))))⁻¹)) := by
        funext N
        rw [add_comm]
      rw [e2]
      exact tendsto_inv_natCast_add _
    have hmul : Filter.Tendsto
      (fun N : ℕ => (2 * b)⁻¹ * ((((a + b) / (2 * b)) + ((N : ℕ) : ℂ))⁻¹))
      Filter.atTop (nhds ((2 * b)⁻¹ * 0)) :=
      tendsto_const_nhds.mul h0
    rwa [mul_zero] at hmul
  have e3 : (fun N : ℕ => ∑ j ∈ Finset.range (2 * N + 1), chapter8Entry8Term a b j)
    = (fun N : ℕ => (∑ j ∈ Finset.range (2 * N), chapter8Entry8Term a b j) +
      chapter8Entry8Term a b (2 * N)) := by
    funext N
    rw [Finset.sum_range_succ]
  rw [e3]
  have hadd := heven.add hodd_term
  simpa using hadd

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[ramanujan_part1_ch8_entry8_digammaseries_complex_digamma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
lemma ramanujan_part1_ch8_entry8_digammaseries_complex_digamma
  {a b : ℂ}
-- given
  (hb : b ≠ 0)
  (hdenom : ∀ j : ℕ, a + b * ((j + 1 : ℕ) : ℂ) ≠ 0) :
-- imply
  HasSum (chapter8Entry8Term a b)
    ((Complex.digamma ((a + 2 * b) / (2 * b)) -
    Complex.digamma ((a + b) / (2 * b))) /
    (2 * b))
    (SummationFilter.conditional ℕ) := by
-- proof
  rw [hv_eq a b hb, div_eq_mul_inv, bridge_iff]
  exact merge_even_odd _ _
    (Seven_limit a b hb hdenom (tail_tendsto a b hb hdenom))
    (Sodd_limit a b hb hdenom (Seven_limit a b hb hdenom (tail_tendsto a b hb hdenom)))

end MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8.Entry8Digammaseries

/--
[ramanujan_part1_ch8_entry8_digammaseries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry8Digammaseries.lean)
-/
@[path]
lemma ramanujan_part1_ch8_entry8_digammaseries
  {a b : ℂ}
-- given
  (hb : b ≠ 0)
  (hleft : Complex.Gamma ((a + 2 * b) / (2 * b)) ≠ 0)
  (hright : Complex.Gamma ((a + b) / (2 * b)) ≠ 0)
  (hdenom : ∀ j : ℕ, a + b * ((j + 1 : ℕ) : ℂ) ≠ 0) :
-- imply
  HasSum (chapter8Entry8Term a b)
    ((chapter8Digamma ((a + 2 * b) / (2 * b)) -
    chapter8Digamma ((a + b) / (2 * b))) /
    (2 * b))
    (SummationFilter.conditional ℕ) := by
-- proof
  have _hleft := hleft
  have _hright := hright
  rw [chapter8Digamma_eq_Complex_digamma, chapter8Digamma_eq_Complex_digamma]
  exact ramanujan_part1_ch8_entry8_digammaseries_complex_digamma a b hb hdenom
end



-- created on 2026-10-20
-- updated on 2026-10-23
