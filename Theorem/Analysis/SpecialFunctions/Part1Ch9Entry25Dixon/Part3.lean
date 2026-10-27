/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Data.Finset.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Basic
import Def.Analysis.SpecialFunctions.Part1Ch9Entry25Dixon.Part3
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry25Dixon

open scoped Topology

open Filter

noncomputable section

theorem dixon_deriv_eq (y : ℂ) (j : ℕ) :
    ((((j + 1 : ℕ)) : ℂ) * y ^ j) / ((((j + 1 : ℕ) : ℝ) : ℂ)) ^ 2
      = y ^ j / ((((j + 1 : ℕ) : ℝ) : ℂ)) := by
  have hc : ((((j + 1 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
    have hpos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  have ecast : ((((j + 1 : ℕ) : ℝ) : ℂ)) = (((j + 1 : ℕ)) : ℂ) :=
    Complex.ofReal_natCast _
  rw [ecast]
  have hn : ((((j + 1 : ℕ))) : ℂ) ≠ 0 := ecast ▸ hc
  field_simp

theorem dixon_hasDerivAt_Li (u : ℂ) (hu : ‖u‖ < 1) :
    HasDerivAt dixonLi (dixonM u) u := by
  set r : ℝ := (1 + ‖u‖) / 2 with hr
  have hr0 : (0 : ℝ) < r := by rw [hr]; have hnn := norm_nonneg u; linarith [hu]
  have hr1 : ‖u‖ < r := by rw [hr]; linarith [hu]
  have hrr : r < 1 := by rw [hr]; linarith [hu]
  have hsum : Summable (fun j : ℕ => r ^ j) :=
    summable_geometric_of_lt_one (le_of_lt hr0) hrr
  have hopen : IsOpen (Metric.ball (0 : ℂ) r) := Metric.isOpen_ball
  have hpre : IsPreconnected (Metric.ball (0 : ℂ) r) :=
    (convex_ball (0 : ℂ) r).isPreconnected
  have hderiv : ∀ j : ℕ, ∀ y ∈ Metric.ball (0 : ℂ) r,
      HasDerivAt (fun v : ℂ => dixonL v j) (y ^ j / ((((j + 1 : ℕ) : ℝ) : ℂ))) y := by
    intro j y _
    have h1 : HasDerivAt (fun v : ℂ => v ^ (j + 1)) ((((j + 1 : ℕ)) : ℂ) * y ^ j) y := by
      have h := hasDerivAt_pow (j + 1) y
      rwa [Nat.add_sub_cancel] at h
    have h2 := h1.div_const (((((j + 1 : ℕ) : ℝ) : ℂ)) ^ 2)
    rw [dixon_deriv_eq] at h2
    exact h2
  have hbound : ∀ j : ℕ, ∀ y ∈ Metric.ball (0 : ℂ) r,
      ‖(y ^ j / ((((j + 1 : ℕ) : ℝ) : ℂ)))‖ ≤ r ^ j := by
    intro j y hy
    have hym : ‖y‖ < r := by
      have hmem := Metric.mem_ball.mp hy
      rwa [dist_zero_right] at hmem
    have h1 : ‖y ^ j / ((((j + 1 : ℕ) : ℝ) : ℂ))‖ = ‖y‖ ^ j / (((j + 1 : ℕ) : ℝ)) := by
      rw [norm_div, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ))]
    rw [h1, div_le_iff₀ (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ))]
    have hc1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
      have hle : (1 : ℕ) ≤ j + 1 := Nat.le_add_left 1 j
      exact_mod_cast hle
    calc ‖y‖ ^ j ≤ r ^ j := pow_le_pow_left₀ (norm_nonneg _) hym.le j
      _ ≤ r ^ j * (((j + 1 : ℕ) : ℝ)) :=
        le_mul_of_one_le_right (pow_nonneg hr0.le _) hc1
  have hy0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_self]; exact hr0
  have hsum0 : Summable (fun j : ℕ => dixonL (0 : ℂ) j) := by
    have h0terms : ∀ j : ℕ, dixonL (0 : ℂ) j = 0 := by
      intro j
      unfold dixonL
      rw [zero_pow (by omega : j + 1 ≠ 0), zero_div]
    have hfun : (fun j : ℕ => dixonL (0 : ℂ) j) = fun _ => (0 : ℂ) :=
      funext (fun j => h0terms j)
    rw [hfun]
    exact summable_zero
  have hy : u ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]; exact hr1
  have h := hasDerivAt_tsum_of_isPreconnected (u := fun j : ℕ => r ^ j)
    (t := Metric.ball (0 : ℂ) r) (g := fun j v => dixonL v j)
    (g' := fun j v => v ^ j / ((((j + 1 : ℕ) : ℝ) : ℂ))) (y₀ := 0) (y := u)
    hsum hopen hpre hderiv hbound hy0 hsum0 hy
  exact h

theorem dixon_uM_eq (u : ℂ) (hu : ‖u‖ < 1) :
    u * dixonM u = -Complex.log (1 - u) := by
  have hlog := Complex.hasSum_taylorSeries_neg_log hu
  have hMsumm : Summable (fun j : ℕ => u ^ j / ((((j + 1 : ℕ) : ℝ) : ℂ))) := by
    apply Summable.of_norm_bounded (g := fun j : ℕ => ‖u‖ ^ j)
      (summable_geometric_of_lt_one (norm_nonneg _) hu)
    intro j
    rw [norm_div, Complex.norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ))]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ))]
    have hc1 : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by
      have hle : (1 : ℕ) ≤ j + 1 := Nat.le_add_left 1 j
      exact_mod_cast hle
    have hnn : (0 : ℝ) ≤ ‖u‖ ^ j := pow_nonneg (norm_nonneg _) _
    exact le_mul_of_one_le_right hnn hc1
  unfold dixonM
  rw [← tsum_mul_left]
  have hshift : (fun j : ℕ => u * (u ^ j / ((((j + 1 : ℕ) : ℝ) : ℂ))))
      = (fun n : ℕ => u ^ (n + 1) / ((((n + 1 : ℕ)) : ℂ))) := by
    funext j
    have ecast : ((((j + 1 : ℕ) : ℝ) : ℂ)) = (((j + 1 : ℕ)) : ℂ) :=
      Complex.ofReal_natCast _
    rw [ecast, ← mul_div_assoc, mul_comm u (u ^ j), ← pow_succ]
  rw [hshift]
  have hshift2 : HasSum (fun n : ℕ => u ^ (n + 1) / ((((n + 1 : ℕ)) : ℂ)))
      (-Complex.log (1 - u)) := by
    have h2 := (hasSum_nat_add_iff' (f := fun n : ℕ => u ^ n / ((((n : ℕ)) : ℂ)))
      (k := 1)).mpr hlog
    rw [Finset.sum_range_one] at h2
    simp only [pow_zero, Nat.cast_zero, div_zero, sub_zero] at h2
    exact h2
  exact hshift2.tsum_eq

end
end Entry25Dixon
end Ramanujan.Part1Ch9
end
