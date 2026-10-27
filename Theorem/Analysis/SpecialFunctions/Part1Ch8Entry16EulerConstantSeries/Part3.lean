/-
Author: @akiezun, Avocado
-/

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.NormNum.Parity
import Def.Analysis.SpecialFunctions.Part1Ch8Entry16EulerConstantSeries.Part3
/-!
# Ramanujan's Notebooks, Part I, Chapter 8

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch8

namespace Entry16Eulerconstantseries

open scoped BigOperators Real

open Topology

noncomputable section

theorem herr (n : ℕ) (hn : 1 ≤ n) : |err n| ≤ 1 / ((n : ℝ)) := by
  have h := H_rate n hn
  have h2 : err n = (Hsum n - Real.log ((n : ℝ))) - Real.eulerMascheroniConstant := by
    unfold err; ring
  rwa [h2]

theorem A_mono (k : ℕ) : Afun k ≤ Afun (k + 1) := by
  have h := A_succ k
  omega

theorem A_ge (N : ℕ) : 3 ^ N ≤ Afun (N + 1) := by
  induction N with
  | zero => decide
  | succ N ih =>
    have hA := A_succ (N + 1)
    have h3 : 3 ^ (N + 1 + 1) = 3 * 3 ^ (N + 1) := by ring
    omega

theorem A_one_le (m : ℕ) (hm : 1 ≤ m) : 1 ≤ Afun m := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  exact le_trans (one_le_pow3 t) (A_ge t)

theorem pow3R (m : ℕ) : (((3 ^ m : ℕ)) : ℝ) = (3:ℝ)^m := by push_cast; ring

theorem Areal_ge (N : ℕ) : (3:ℝ)^N ≤ ((Afun (N+1) : ℝ)) := by
  have h := A_ge N
  have h3 : (((3 ^ N : ℕ)) : ℝ) = (3:ℝ)^N := pow3R N
  calc (3:ℝ)^N = (((3 ^ N : ℕ)) : ℝ) := h3.symm
    _ ≤ ((Afun (N+1) : ℝ)) := by exact_mod_cast h

theorem Apos (m : ℕ) (hm : 1 ≤ m) : 0 < ((Afun m : ℝ)) := by
  have h1 : (1:ℝ) ≤ ((Afun m : ℝ)) := by exact_mod_cast A_one_le m hm
  linarith

theorem errA (m : ℕ) (hm : 1 ≤ m) : |err (Afun m)| ≤ 1 / ((Afun m : ℝ)) :=
  herr (Afun m) (A_one_le m hm)

theorem hlogbound (x : ℝ) (hx0 : 0 ≤ x) (hx12 : x ≤ 1 / 2) :
    |Real.log (1 - x)| ≤ 2 * x := by
  have h1x : (0 : ℝ) < 1 - x := by linarith
  have h1x_le : (1 : ℝ) - x ≤ 1 := by linarith
  have hlog_nonpos : Real.log (1 - x) ≤ 0 := Real.log_nonpos (by linarith) h1x_le
  rw [abs_of_nonpos hlog_nonpos]
  have h1 : -Real.log (1 - x) = Real.log (1 / (1 - x)) := by
    rw [Real.log_div (by norm_num) (ne_of_gt h1x)]
    simp [Real.log_one]
  rw [h1]
  have h2 : Real.log (1 / (1 - x)) ≤ 1 / (1 - x) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h3 : (1 : ℝ) / (1 - x) - 1 = x / (1 - x) := by
    field_simp
    ring
  have h4 : x / (1 - x) ≤ 2 * x := by
    rw [div_le_iff₀ h1x]
    nlinarith [hx0, hx12]
  linarith [h2, h3, h4]

theorem rmem (m : ℕ) (hm : 1 ≤ m) : 0 ≤ (1/3:ℝ)^m ∧ (1/3:ℝ)^m ≤ 1/2 := by
  constructor
  · positivity
  · calc (1/3:ℝ)^m ≤ (1/3:ℝ)^1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ = 1/3 := pow_one _
      _ ≤ 1/2 := by norm_num

theorem logA (m : ℕ) (hm : 1 ≤ m) :
    Real.log ((Afun m : ℝ)) = (m : ℝ) * Real.log 3 - Real.log 2 + Real.log (1 - (1/3:ℝ)^m) := by
  have hA := A_cast m
  have h3 : (((3 ^ m : ℕ)) : ℝ) = (3:ℝ)^m := pow3R m
  have hmpos : (0:ℝ) < (3:ℝ)^m := by positivity
  have h3ne : (3:ℝ)^m ≠ 0 := ne_of_gt hmpos
  have hrm : (1/3:ℝ)^m ≤ 1/3 := by
    calc (1/3:ℝ)^m ≤ (1/3:ℝ)^1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ = 1/3 := pow_one _
  have h1r : (0:ℝ) < 1 - (1/3:ℝ)^m := by linarith
  have h1rne : (1:ℝ) - (1/3:ℝ)^m ≠ 0 := ne_of_gt h1r
  have hmul : (3:ℝ)^m * (1/3:ℝ)^m = 1 := by
    rw [← mul_pow]
    norm_num
  have hdecomp : ((Afun m : ℝ)) = (3:ℝ)^m * (1 - (1/3:ℝ)^m) / 2 := by
    rw [hA, h3]
    have h2 : (3:ℝ)^m * (1 - (1/3:ℝ)^m) = (3:ℝ)^m - 1 := by
      rw [mul_sub, mul_one, hmul]
    rw [h2]
  rw [hdecomp, Real.log_div (mul_ne_zero h3ne h1rne) (by norm_num),
    Real.log_mul h3ne h1rne, Real.log_pow]
  ring

theorem L1lim : Filter.Tendsto
    (fun N : ℕ => (((N + 1 : ℕ) : ℝ)) *
        (Real.log ((Afun (N+1+1) : ℝ)) - Real.log ((Afun (N+1) : ℝ))) - Real.log ((Afun (N+1) : ℝ)))
    Filter.atTop (nhds (Real.log 2)) := by
  have hexpr : ∀ N : ℕ, ((((N+1:ℕ)):ℝ)) * (Real.log ((Afun (N+1+1):ℝ)) - Real.log ((Afun (N+1):ℝ)))
      - Real.log ((Afun (N+1):ℝ)) =
      Real.log 2 + (((((N+1:ℕ)):ℝ)) *
          (Real.log (1 - (1/3:ℝ)^(N+1+1)) - Real.log (1 - (1/3:ℝ)^(N+1))) - Real.log
              (1 - (1/3:ℝ)^(N+1))) := by
    intro N
    have h1 := logA (N+1+1) (by omega)
    have h2 := logA (N+1) (by omega)
    rw [h1, h2]
    push_cast
    ring
  have hE : Filter.Tendsto (fun N : ℕ => ((((N+1:ℕ)):ℝ)) *
      (Real.log (1 - (1/3:ℝ)^(N+1+1)) - Real.log (1 - (1/3:ℝ)^(N+1))) - Real.log
          (1 - (1/3:ℝ)^(N+1))) Filter.atTop (nhds 0) := by
    have hb : ∀ N : ℕ, ‖((((N+1:ℕ)):ℝ)) *
        (Real.log (1 - (1/3:ℝ)^(N+1+1)) - Real.log (1 - (1/3:ℝ)^(N+1))) - Real.log
            (1 - (1/3:ℝ)^(N+1))‖ ≤
        2 * ((((N:ℝ))+1) * (1/3:ℝ)^(N+1+1)) + 2 * ((((N:ℝ))+1) * (1/3:ℝ)^(N+1)) + 2 *
            (1/3:ℝ)^(N+1) := by
      intro N
      have hr1 := rmem (N+1+1) (by omega)
      have hr2 := rmem (N+1) (by omega)
      have hb1 : |Real.log (1 - (1/3:ℝ)^(N+1+1))| ≤ 2 * (1/3:ℝ)^(N+1+1) := hlogbound _ hr1.1 hr1.2
      have hb2 : |Real.log (1 - (1/3:ℝ)^(N+1))| ≤ 2 * (1/3:ℝ)^(N+1) := hlogbound _ hr2.1 hr2.2
      have hcast : (((N+1:ℕ)):ℝ) = ((N:ℝ)) + 1 := by push_cast; ring
      set la := Real.log (1 - (1/3:ℝ)^(N+1+1)) with hla
      set lb := Real.log (1 - (1/3:ℝ)^(N+1)) with hlb
      rw [Real.norm_eq_abs, hcast]
      have hPn : (0:ℝ) ≤ ((N:ℝ)) + 1 := by positivity
      have e1 : (((N:ℝ))+1) * |la| ≤ (((N:ℝ))+1) * (2 * (1/3:ℝ)^(N+1+1)) :=
        mul_le_mul_of_nonneg_left hb1 hPn
      have e2 : (((N:ℝ))+1) * |lb| ≤ (((N:ℝ))+1) * (2 * (1/3:ℝ)^(N+1)) :=
        mul_le_mul_of_nonneg_left hb2 hPn
      have hsub : |la - lb| ≤ |la| + |lb| := abs_sub _ _
      have hmul : (((N:ℝ))+1) * |la - lb| ≤ (((N:ℝ))+1) * |la| + (((N:ℝ))+1) * |lb| := by
        have h := mul_le_mul_of_nonneg_left hsub hPn
        rwa [mul_add] at h
      have h3 : |(((N:ℝ))+1) * (la - lb)| = (((N:ℝ))+1) * |la - lb| := by
        rw [abs_mul, abs_of_nonneg hPn]
      have hfin : |(((N:ℝ))+1) * (la - lb) - lb| ≤ (((N:ℝ))+1) * |la| + (((N:ℝ))+1) * |lb| +
          |lb| := by
        have h1 : |(((N:ℝ))+1) * (la - lb) - lb| ≤ |(((N:ℝ))+1) * (la - lb)| + |lb| := abs_sub _ _
        linarith [h1, hmul, h3]
      calc |(((N:ℝ))+1) * (la - lb) - lb|
          ≤ (((N:ℝ))+1) * |la| + (((N:ℝ))+1) * |lb| + |lb| := hfin
        _ ≤ (((N:ℝ))+1) * (2 * (1/3:ℝ)^(N+1+1)) + (((N:ℝ))+1) * (2 * (1/3:ℝ)^(N+1)) + 2 *
            (1/3:ℝ)^(N+1) := by
            linarith [e1, e2, hb2]
        _ = 2 * ((((N:ℝ))+1) * (1/3:ℝ)^(N+1+1)) + 2 * ((((N:ℝ))+1) * (1/3:ℝ)^(N+1)) + 2 *
            (1/3:ℝ)^(N+1) := by
            ring
    have ht1 : Filter.Tendsto (fun N : ℕ => 2 * ((((N:ℝ))+1) * (1/3:ℝ)^(N+1+1))) Filter.atTop
        (nhds 0) := by
      have h0 := key_decay.const_mul (2*(1/3:ℝ)^(1+1))
      rw [mul_zero] at h0
      refine h0.congr (fun N => ?_)
      ring
    have ht2 : Filter.Tendsto (fun N : ℕ => 2 * ((((N:ℝ))+1) * (1/3:ℝ)^(N+1))) Filter.atTop
        (nhds 0) := by
      have h0 := key_decay.const_mul (2*(1/3:ℝ))
      rw [mul_zero] at h0
      refine h0.congr (fun N => ?_)
      ring
    have ht3 : Filter.Tendsto (fun N : ℕ => 2 * (1/3:ℝ)^(N+1)) Filter.atTop (nhds 0) := by
      have h0 := geo_third.const_mul (2*(1/3:ℝ))
      rw [mul_zero] at h0
      refine h0.congr (fun N => ?_)
      ring
    have hB : Filter.Tendsto (fun N : ℕ => 2 * ((((N:ℝ))+1) * (1/3:ℝ)^(N+1+1)) + 2 *
        ((((N:ℝ))+1) * (1/3:ℝ)^(N+1)) + 2 * (1/3:ℝ)^(N+1)) Filter.atTop (nhds 0) := by
      have h := (ht1.add ht2).add ht3
      simpa using h
    exact squeeze_zero_norm hb hB
  have hadd : Filter.Tendsto (fun N : ℕ => Real.log 2 +
      (((((N+1:ℕ)):ℝ)) * (Real.log (1 - (1/3:ℝ)^(N+1+1)) - Real.log (1 - (1/3:ℝ)^(N+1))) - Real.log
          (1 - (1/3:ℝ)^(N+1)))) Filter.atTop (nhds (Real.log 2 + 0)) :=
    tendsto_const_nhds.add hE
  rw [add_zero] at hadd
  refine hadd.congr (fun N => ?_)
  exact (hexpr N).symm

theorem E2lim : Filter.Tendsto
    (fun N : ℕ => (((N + 1 : ℕ) : ℝ)) * (err (Afun (N+1+1)) - err (Afun (N+1))) - err (Afun (N+1)))
    Filter.atTop (nhds 0) := by
  have hb : ∀ N : ℕ, ‖(((N+1:ℕ)):ℝ) * (err (Afun (N+1+1)) - err (Afun (N+1))) - err (Afun (N+1))‖ ≤
      2 * ((((N:ℝ))+1) * (1/3:ℝ)^N) + (1/3:ℝ)^N := by
    intro N
    have e1 := errA (N+1) (by omega)
    have e2 := errA (N+1+1) (by omega)
    have hApos : (0:ℝ) < ((Afun (N+1) : ℝ)) := Apos _ (by omega)
    have h3pos : (0:ℝ) < (3:ℝ)^N := by positivity
    have hAge : (3:ℝ)^N ≤ ((Afun (N+1) : ℝ)) := Areal_ge N
    have hmono : ((Afun (N+1) : ℝ)) ≤ ((Afun (N+1+1) : ℝ)) := by
      have h := A_mono (N+1)
      exact_mod_cast h
    have h1A : 1 / ((Afun (N+1):ℝ)) ≤ 1 / (3:ℝ)^N := one_div_le_one_div_of_le h3pos hAge
    have h1A2 : 1 / ((Afun (N+1+1):ℝ)) ≤ 1 / ((Afun (N+1):ℝ)) := one_div_le_one_div_of_le hApos
        hmono
    have f1 : |err (Afun (N+1+1))| ≤ 1 / ((Afun (N+1):ℝ)) := le_trans e2 h1A2
    have hcast : (((N+1:ℕ)):ℝ) = ((N:ℝ)) + 1 := by push_cast; ring
    have hrw : (1/3:ℝ)^N = 1/(3:ℝ)^N := by rw [div_pow, one_pow]
    rw [Real.norm_eq_abs, hcast]
    set ea := err (Afun (N+1+1)) with hea
    set eb := err (Afun (N+1)) with heb
    have hPn : (0:ℝ) ≤ ((N:ℝ)) + 1 := by positivity
    have g1 : (((N:ℝ))+1) * |ea| ≤ (((N:ℝ))+1) * (1/(3:ℝ)^N) :=
      mul_le_mul_of_nonneg_left (le_trans f1 h1A) hPn
    have g2 : (((N:ℝ))+1) * |eb| ≤ (((N:ℝ))+1) * (1/(3:ℝ)^N) :=
      mul_le_mul_of_nonneg_left (le_trans e1 h1A) hPn
    have heb2 : |eb| ≤ (1/3:ℝ)^N := by rw [hrw]; exact le_trans e1 h1A
    have hsub : |ea - eb| ≤ |ea| + |eb| := abs_sub _ _
    have hmul : (((N:ℝ))+1) * |ea - eb| ≤ (((N:ℝ))+1) * |ea| + (((N:ℝ))+1) * |eb| := by
      have h := mul_le_mul_of_nonneg_left hsub hPn
      rwa [mul_add] at h
    have hfin : |(((N:ℝ))+1) * (ea - eb) - eb| ≤ (((N:ℝ))+1) * |ea| + (((N:ℝ))+1) * |eb| +
        |eb| := by
      have h1 : |(((N:ℝ))+1) * (ea - eb) - eb| ≤ |(((N:ℝ))+1) * (ea - eb)| + |eb| := abs_sub _ _
      have h3 : |(((N:ℝ))+1) * (ea - eb)| = (((N:ℝ))+1) * |ea - eb| := by
        rw [abs_mul, abs_of_nonneg hPn]
      linarith [h1, hmul, h3]
    have h1A' : (1/(3:ℝ)^N) = (1/3:ℝ)^N := hrw.symm
    rw [h1A'] at g1 g2
    linarith [hfin, g1, g2, heb2]
  have hB : Filter.Tendsto (fun N : ℕ => 2 * ((((N:ℝ))+1) * (1/3:ℝ)^N) + (1/3:ℝ)^N) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun N : ℕ => 2 * ((((N:ℝ))+1) * (1/3:ℝ)^N)) Filter.atTop
        (nhds 0) := by
      have h0 := key_decay.const_mul 2
      rw [mul_zero] at h0
      refine h0.congr (fun N => ?_)
      ring
    have h := h1.add geo_third
    simpa using h
  exact squeeze_zero_norm hb hB

theorem hlim : Filter.Tendsto (fun N : ℕ => 2 * ∑ k ∈ Finset.range (N + 1), Tfun k)
    Filter.atTop (nhds (Real.log 2 - Real.eulerMascheroniConstant)) := by
  have e1 : ∀ N : ℕ, 2 * ∑ k ∈ Finset.range (N + 1), Tfun k =
      ((((N+1:ℕ)):ℝ) * (Real.log ((Afun (N+1+1):ℝ)) - Real.log ((Afun (N+1):ℝ))) - Real.log
          ((Afun (N+1):ℝ)) - Real.eulerMascheroniConstant) +
      ((((N+1:ℕ)):ℝ) * (err (Afun (N+1+1)) - err (Afun (N+1))) - err (Afun (N+1))) := by
    intro N
    have hKI := key_identity (N + 1)
    have h2a : Hsum (Afun (N+1+1)) = Real.log ((Afun (N+1+1):ℝ)) + Real.eulerMascheroniConstant +
        err (Afun (N+1+1)) := by
      unfold err; ring
    have h2b : Hsum (Afun (N+1)) = Real.log ((Afun (N+1):ℝ)) + Real.eulerMascheroniConstant + err
        (Afun (N+1)) := by
      unfold err; ring
    rw [h2a, h2b] at hKI
    linear_combination hKI
  have hcomb : Filter.Tendsto
      (fun N : ℕ => ((((N+1:ℕ)):ℝ) * (Real.log ((Afun (N+1+1):ℝ)) - Real.log ((Afun (N+1):ℝ))) -
          Real.log ((Afun (N+1):ℝ)) - Real.eulerMascheroniConstant) +
        ((((N+1:ℕ)):ℝ) * (err (Afun (N+1+1)) - err (Afun (N+1))) - err (Afun (N+1))))
      Filter.atTop (nhds ((Real.log 2 - Real.eulerMascheroniConstant) + 0)) :=
    (L1lim.sub_const Real.eulerMascheroniConstant).add E2lim
  rw [add_zero] at hcomb
  refine hcomb.congr (fun N => ?_)
  exact (e1 N).symm

theorem hS : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), Tfun k)
    Filter.atTop (nhds (∑' k, Tfun k)) := by
  have hP := summable_tfun.hasSum.tendsto_sum_nat
  have hT := summable_tfun.tendsto_atTop_zero
  have hPS : Filter.Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, Tfun k) + Tfun N)
      Filter.atTop (nhds ((∑' k, Tfun k) + 0)) := hP.add hT
  rw [add_zero] at hPS
  refine hPS.congr (fun N => ?_)
  exact (Finset.sum_range_succ Tfun N).symm

theorem hfinal : 2 * ∑' k, Tfun k = Real.log 2 - Real.eulerMascheroniConstant := by
  have h2S : Filter.Tendsto (fun N : ℕ => 2 * ∑ k ∈ Finset.range (N + 1), Tfun k)
      Filter.atTop (nhds (2 * ∑' k, Tfun k)) :=
    tendsto_const_nhds.mul hS
  exact tendsto_nhds_unique h2S hlim

theorem main_result : Summable Tfun ∧
    Real.eulerMascheroniConstant = Real.log 2 - 2 * ∑' k, Tfun k := by
  refine ⟨summable_tfun, ?_⟩
  linarith [hfinal]

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8, Entry 16.

Proves `Wanted` entry `ramanujan_part1_ch8_entry16_eulerconstantseries`.
-/
theorem ramanujan_part1_ch8_entry16_eulerconstantseries :
    let A : ℕ → ℕ := fun k => (3 ^ k - 1) / 2
    let term : ℕ → ℝ := fun k =>
      ((k + 1 : ℕ) : ℝ) *
        ∑ j ∈ Finset.Icc (A k + 1) (A (k + 1)),
          (1 : ℝ) / ((3 * (j : ℝ)) ^ 3 - 3 * (j : ℝ))
    Summable term ∧
      Real.eulerMascheroniConstant = Real.log 2 - 2 * ∑' k : ℕ, term k := by
  exact main_result

end
end Entry16Eulerconstantseries
end Ramanujan.Part1Ch8
end
