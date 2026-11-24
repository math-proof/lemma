module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Def.Analysis.SpecialFunctions.Part1Ch9Entry20Piseries1.Part9


public section

/-
Author: @akiezun, Avocado
-/
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/
section

namespace Ramanujan.Part1Ch9

namespace Entry20Piseries1

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem auxAr_tendsto (x : ℝ) :
    Filter.Tendsto (fun r => auxAr r x) (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (auxA_fourier x)) := by
  have hbound : Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2)) :=
    aux_one_div_sq_summable
  have hab : ∀ j : ℕ, Filter.Tendsto (fun r => auxAr_term r x j)
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (chapter9SineFourierTwoTerm x j)) := by
    intro j
    have hpow : Filter.Tendsto (fun r : ℝ => r ^ (j + 1)) (nhds (1 : ℝ)) (nhds 1) := by
      have hcont : ContinuousAt (fun r : ℝ => r ^ (j + 1)) 1 :=
        continuousAt_id.pow _
      simpa using hcont.tendsto
    have hpowW : Filter.Tendsto (fun r : ℝ => r ^ (j + 1))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 1) :=
      hpow.mono_left nhdsWithin_le_nhds
    have hmul := hpowW.mul_const (chapter9SineFourierTwoTerm x j)
    have hone : (1 : ℝ) * chapter9SineFourierTwoTerm x j =
        chapter9SineFourierTwoTerm x j := one_mul _
    rw [hone] at hmul
    have heq : (fun r => r ^ (j + 1) * chapter9SineFourierTwoTerm x j) =
        (fun r => auxAr_term r x j) := by
      funext r
      unfold auxAr_term chapter9SineFourierTwoTerm
      simp only
      ring
    rwa [heq] at hmul
  have hIoo : Set.Ioo (0 : ℝ) 2 ∈ nhds (1 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hIooW : Set.Ioo 0 2 ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) :=
    mem_nhdsWithin_of_mem_nhds hIoo
  have hIioW : Set.Iio (1 : ℝ) ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) :=
    self_mem_nhdsWithin
  have h_bound : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1),
      ∀ j : ℕ, ‖auxAr_term r x j‖ ≤ (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
    filter_upwards [hIooW, hIioW] with r hrIoo hrIio j
    have hr0 : 0 ≤ r := le_of_lt (Set.mem_Ioo.mp hrIoo).1
    have hr1 : r ≤ 1 := le_of_lt hrIio
    have hpow_le : r ^ (j + 1) ≤ 1 := pow_le_one₀ hr0 hr1
    have hpow_nn : (0 : ℝ) ≤ r ^ (j + 1) := pow_nonneg hr0 _
    have hsin : |Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x)| ≤ 1 :=
      Real.abs_sin_le_one _
    have hpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
      apply pow_pos
      exact Nat.cast_pos.mpr (Nat.succ_pos j)
    unfold auxAr_term
    rw [Real.norm_eq_abs, abs_div, abs_mul]
    have habs2 : |((((j + 1 : ℕ)) : ℝ) ^ 2)| = ((((j + 1 : ℕ)) : ℝ) ^ 2) :=
      abs_of_pos hpos
    rw [habs2, abs_of_nonneg hpow_nn]
    calc r ^ (j + 1) * |Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x)| /
          ((((j + 1 : ℕ)) : ℝ) ^ 2)
        = (r ^ (j + 1) * |Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x)|) *
          (1 / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by ring
      _ ≤ (1 * 1) * (1 / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
          apply mul_le_mul _ le_rfl (by positivity) (by positivity)
          exact mul_le_mul hpow_le hsin (by positivity) (by positivity)
      _ = 1 / ((((j + 1 : ℕ)) : ℝ) ^ 2) := by ring
  have hmain := tendsto_tsum_of_dominated_convergence hbound hab h_bound
  have efun1 : (fun r => ∑' j : ℕ, auxAr_term r x j) = (fun r => auxAr r x) := by
    funext r
    rfl
  have efun2 : (∑' j : ℕ, chapter9SineFourierTwoTerm x j) = auxA_fourier x := rfl
  rw [efun1, efun2] at hmain
  exact hmain

theorem aux_sin_ge_sin_a {a b : ℝ} (ha0 : 0 < a)
    (hb1 : b < Real.pi / 2) {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    Real.sin a ≤ Real.sin x := by
  have hx1 : a < x := (Set.mem_Ioo.mp hx).1
  have hx2 : x < b := (Set.mem_Ioo.mp hx).2
  have h1 : -(Real.pi / 2) ≤ a := by linarith [Real.pi_pos]
  have h2 : x ≤ Real.pi / 2 := le_of_lt (lt_trans hx2 hb1)
  have h3 : a ≤ x := le_of_lt hx1
  exact Real.sin_le_sin_of_le_of_le_pi_div_two h1 h2 h3

end
end Entry20Piseries1
end Ramanujan.Part1Ch9
end
