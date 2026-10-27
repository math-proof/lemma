/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch9Entry20Piseries1.Part11
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

theorem auxG_hasDerivAt {x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt auxG ((x₀ ^ 2 / 2) * (Real.cos x₀ / Real.sin x₀)) x₀ := by
  have hx0_ne : x₀ ≠ 0 := ne_of_gt (Set.mem_Ioo.mp hx₀).1
  have h2sin_pos : (0 : ℝ) < 2 * Real.sin x₀ := by
    have h := aux_sin_pos_of_Ioo hx₀
    linarith
  have hlog := aux_logterm_hasDerivAt hx0_ne h2sin_pos
  have hA : HasDerivAt auxA_fourier (auxA_deriv_lim x₀) x₀ :=
    auxA_fourier_hasDerivAt hx₀
  have hid : HasDerivAt (fun x : ℝ => x / 2) ((1 : ℝ) / 2) x₀ := by
    have h := (hasDerivAt_id x₀).div_const (2 : ℝ)
    simpa using h
  have hleft : HasDerivAt (fun x : ℝ => x / 2 * auxA_fourier x)
      ((1 : ℝ) / 2 * auxA_fourier x₀ + x₀ / 2 * auxA_deriv_lim x₀) x₀ :=
    hid.mul hA
  have hB : HasDerivAt auxB_fourier (-2 * auxA_fourier x₀) x₀ :=
    aux_cosine_hasDerivAt x₀
  have hB4 : HasDerivAt (fun x : ℝ => (1 / 4 : ℝ) * auxB_fourier x)
      ((1 / 4 : ℝ) * (-2 * auxA_fourier x₀)) x₀ :=
    hB.const_mul (1 / 4 : ℝ)
  have hsum : HasDerivAt
      (fun x : ℝ => chapter9Entry20LogTerm x + x / 2 * auxA_fourier x +
        (1 / 4 : ℝ) * auxB_fourier x)
      ((x₀ * Real.log (2 * Real.sin x₀) + x₀ ^ 2 / 2 * (Real.cos x₀ / Real.sin x₀)) +
        ((1 : ℝ) / 2 * auxA_fourier x₀ + x₀ / 2 * auxA_deriv_lim x₀) +
        ((1 / 4 : ℝ) * (-2 * auxA_fourier x₀))) x₀ :=
    (hlog.add hleft).add hB4
  have hconst : HasDerivAt (fun _ : ℝ => chapter9ZetaThree / 4) 0 x₀ :=
    hasDerivAt_const x₀ (chapter9ZetaThree / 4)
  have hfull : HasDerivAt auxG
      (((x₀ * Real.log (2 * Real.sin x₀) +
        x₀ ^ 2 / 2 * (Real.cos x₀ / Real.sin x₀)) +
        ((1 : ℝ) / 2 * auxA_fourier x₀ + x₀ / 2 * auxA_deriv_lim x₀) +
        ((1 / 4 : ℝ) * (-2 * auxA_fourier x₀))) - 0) x₀ :=
    hsum.sub hconst
  have hval : (((x₀ * Real.log (2 * Real.sin x₀) +
      x₀ ^ 2 / 2 * (Real.cos x₀ / Real.sin x₀)) +
        ((1 : ℝ) / 2 * auxA_fourier x₀ + x₀ / 2 * auxA_deriv_lim x₀) +
        ((1 / 4 : ℝ) * (-2 * auxA_fourier x₀))) - 0) =
      (x₀ ^ 2 / 2) * (Real.cos x₀ / Real.sin x₀) := by
    rw [auxA_deriv_lim_eq x₀]
    ring
  rw [hval] at hfull
  exact hfull

theorem aux_logterm_continuousOn_Icc {y : ℝ}
    (hy : y ≤ Real.pi / 2) :
    ContinuousOn chapter9Entry20LogTerm (Set.Icc 0 y) := by
  intro z hz
  by_cases hz0 : z = 0
  · subst hz0
    have h0 : chapter9Entry20LogTerm 0 = 0 := by
      unfold chapter9Entry20LogTerm
      simp
    rw [Metric.continuousWithinAt_iff', h0]
    intro ε hε
    have hlim := Metric.tendsto_nhds.mp aux_logterm_tendsto_nhdsGT ε hε
    rw [eventually_nhdsWithin_iff] at hlim ⊢
    filter_upwards [hlim] with x hx
    intro hxIcc
    by_cases hx0 : x = 0
    · subst hx0
      rw [h0, dist_self]
      exact hε
    · exact hx (Set.mem_Ioi.mpr (lt_of_le_of_ne' (Set.mem_Icc.mp hxIcc).1 hx0))
  · have hzpos : 0 < z := lt_of_le_of_ne' (Set.mem_Icc.mp hz).1 hz0
    have hzlt : z < Real.pi := by
      have h2 : z ≤ y := (Set.mem_Icc.mp hz).2
      linarith [Real.pi_pos]
    have hsin_pos : 0 < Real.sin z := Real.sin_pos_of_pos_of_lt_pi hzpos hzlt
    have h2sin_pos : (0 : ℝ) < 2 * Real.sin z := by linarith
    exact (aux_logterm_hasDerivAt hz0 h2sin_pos).continuousAt.continuousWithinAt

theorem auxG_continuousOn_Icc {y : ℝ}
    (hy : y ≤ Real.pi / 2) :
    ContinuousOn auxG (Set.Icc 0 y) := by
  have hlog := aux_logterm_continuousOn_Icc hy
  have hA : ContinuousOn (fun x : ℝ => x / 2 * auxA_fourier x)
      (Set.Icc 0 y) := by
    have h1 : ContinuousOn (fun x : ℝ => x / 2) (Set.Icc 0 y) :=
      (continuous_id'.div_const 2).continuousOn
    have h2 : ContinuousOn auxA_fourier (Set.Icc 0 y) :=
      aux_sine_continuous.continuousOn
    exact h1.mul h2
  have hB : ContinuousOn (fun x : ℝ => (1 / 4 : ℝ) * auxB_fourier x)
      (Set.Icc 0 y) := by
    have h : ContinuousOn auxB_fourier (Set.Icc 0 y) :=
      aux_cosine_continuous.continuousOn
    have hc : ContinuousOn (fun _ : ℝ => (1 / 4 : ℝ)) (Set.Icc 0 y) :=
      continuousOn_const
    exact hc.mul h
  have hsum : ContinuousOn
      (fun x : ℝ => chapter9Entry20LogTerm x + x / 2 * auxA_fourier x +
        (1 / 4 : ℝ) * auxB_fourier x) (Set.Icc 0 y) :=
    (hlog.add hA).add hB
  have h : ContinuousOn
      (fun x : ℝ => (chapter9Entry20LogTerm x + x / 2 * auxA_fourier x +
        (1 / 4 : ℝ) * auxB_fourier x) - chapter9ZetaThree / 4)
      (Set.Icc 0 y) :=
    hsum.sub continuousOn_const
  exact h

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.

Proves `Wanted` entry `ramanujan_part1_ch9_entry20_piseries1`.
-/
theorem ramanujan_part1_ch9_entry20_piseries1 (x : ℝ) (hx : |x| ≤ Real.pi / 2) :
    (x ≠ 0 → 0 < |2 * Real.sin x|) ∧
      Summable chapter9ZetaThreeTerm ∧
      Summable (chapter9Entry23FactorialTerm x) ∧
      Summable (chapter9SineFourierTwoTerm x) ∧
      Summable (chapter9CosineFourierThreeTerm x) ∧
      (∑' k : ℕ, chapter9Entry23FactorialTerm x k) =
        chapter9Entry20LogTerm x +
          x / 2 * ∑' j : ℕ, chapter9SineFourierTwoTerm x j +
          (1 / 4 : ℝ) * ∑' j : ℕ, chapter9CosineFourierThreeTerm x j -
          chapter9ZetaThree / 4 := by
  refine ⟨?_, aux_zetaThree_summable, aux_factorial_summable x,
    aux_sineTwo_summable x, aux_cosineThree_summable x, ?_⟩
  · intro hx0
    have hsin_ne : Real.sin x ≠ 0 := by
      rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · have hpos : 0 < -x := neg_pos.mpr hneg
        have habs : |-x| ≤ Real.pi / 2 := by rwa [abs_neg]
        have hle : -x ≤ Real.pi / 2 := le_trans (le_abs_self _) habs
        have hlt : -x < Real.pi := by linarith [Real.pi_pos]
        have h := Real.sin_pos_of_pos_of_lt_pi hpos hlt
        rw [Real.sin_neg] at h
        intro hcon
        rw [hcon, neg_zero] at h
        exact lt_irrefl 0 h
      · have hle : x ≤ Real.pi / 2 := le_trans (le_abs_self _) hx
        have hlt : x < Real.pi := by linarith [Real.pi_pos]
        have h := Real.sin_pos_of_pos_of_lt_pi hpos hlt
        exact ne_of_gt h
    have hpos : 0 < |Real.sin x| := abs_pos.mpr hsin_ne
    have heq : |2 * Real.sin x| = 2 * |Real.sin x| := by
      rw [abs_mul]
      norm_num
    rw [heq]
    linarith
  · -- Series equality: both sides are even, so it suffices to prove it for `0 ≤ x`.
    have hcore : ∀ y : ℝ, 0 ≤ y → |y| ≤ Real.pi / 2 →
        (∑' k : ℕ, chapter9Entry23FactorialTerm y k) =
          chapter9Entry20LogTerm y +
            y / 2 * ∑' j : ℕ, chapter9SineFourierTwoTerm y j +
            (1 / 4 : ℝ) * ∑' j : ℕ, chapter9CosineFourierThreeTerm y j -
            chapter9ZetaThree / 4 := by
      intro y hy0 hy
      by_cases hy0' : y = 0
      · subst hy0'
        rw [aux_factorial_tsum_zero]
        exact aux_rhs_zero.symm
      · have hypos : 0 < y := lt_of_le_of_ne' hy0 hy0'
        have hy_le : y ≤ Real.pi / 2 := le_trans (le_abs_self y) hy
        have hF0 : auxF 0 = 0 := aux_factorial_tsum_zero
        have hG0 : auxG 0 = 0 := aux_rhs_zero
        have hcont : ContinuousOn (fun z => auxF z - auxG z) (Set.Icc 0 y) :=
          aux_factorial_continuous.continuousOn.sub
            (auxG_continuousOn_Icc hy_le)
        have hderiv : ∀ z ∈ Set.Ioo 0 y,
            HasDerivAt (fun z => auxF z - auxG z) 0 z := by
          intro z hz
          have hzIoo : z ∈ Set.Ioo 0 (Real.pi / 2) := by
            have h1 : 0 < z := (Set.mem_Ioo.mp hz).1
            have h2 : z < y := (Set.mem_Ioo.mp hz).2
            exact ⟨h1, lt_of_lt_of_le h2 hy_le⟩
          have hF := auxF_hasDerivAt hzIoo
          have hG := auxG_hasDerivAt hzIoo
          have h := hF.sub hG
          simp only [sub_self] at h
          exact h
        obtain ⟨c, _, hc⟩ :=
          exists_hasDerivAt_eq_slope (fun z => auxF z - auxG z) (fun _ => 0)
            hypos hcont hderiv
        simp only [hF0, hG0, sub_self (0 : ℝ), sub_zero (auxF y - auxG y)] at hc
        have hne : y - 0 ≠ 0 := ne_of_gt (by linarith)
        have h0 : (auxF y - auxG y) / (y - 0) = 0 := hc.symm
        rw [div_eq_zero_iff] at h0
        have hnum : auxF y - auxG y = 0 := h0.resolve_right hne
        have heq : auxF y = auxG y := sub_eq_zero.mp hnum
        exact heq
    by_cases hx0 : 0 ≤ x
    · exact hcore x hx0 hx
    · have hnx : 0 ≤ -x := le_of_lt (neg_pos.mpr (lt_of_not_ge hx0))
      have habs : |-x| ≤ Real.pi / 2 := by rwa [abs_neg]
      have h := hcore (-x) hnx habs
      rw [← aux_factorial_tsum_even x, ← aux_rhs_even x]
      exact h

end
end Entry20Piseries1
end Ramanujan.Part1Ch9
end
