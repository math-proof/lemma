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
import Def.Analysis.SpecialFunctions.Part1Ch9Entry20Piseries1.Part4
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

theorem auxK_zero : auxK 0 = 0 := by
  unfold auxK
  rw [Real.sin_zero, auxP_zero, mul_zero]

theorem auxK_hasDerivAt {x : ℝ}
    (hx : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    HasDerivAt auxK 1 x := by
  have hsin : |Real.sin x| < 1 := aux_sin_abs_lt_one hx
  have hP : HasDerivAt auxP (∑' k : ℕ, auxPderiv_term (Real.sin x) k) (Real.sin x) :=
    auxP_hasDerivAt hsin
  have hcomp0 := hP.comp x (Real.hasDerivAt_sin x)
  simp only [Function.comp_def] at hcomp0
  rw [mul_comm (∑' k : ℕ, auxPderiv_term (Real.sin x) k) (Real.cos x)] at hcomp0
  have hcomp : HasDerivAt (fun y => auxP (Real.sin y))
      (Real.cos x * (∑' k : ℕ, auxPderiv_term (Real.sin x) k)) x :=
    hcomp0
  have hmul : HasDerivAt (fun y => Real.cos y * auxP (Real.sin y))
      (-Real.sin x * auxP (Real.sin x) +
        Real.cos x * (Real.cos x * (∑' k : ℕ, auxPderiv_term (Real.sin x) k))) x :=
    (Real.hasDerivAt_cos x).mul hcomp
  have efun : (fun y => Real.cos y * auxP (Real.sin y)) = auxK := by
    funext y
    rfl
  rw [efun] at hmul
  have hode := auxP_ode hsin
  have hcos : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
    have h := Real.sin_sq_add_cos_sq x
    linarith
  have hval : -Real.sin x * auxP (Real.sin x) +
      Real.cos x * (Real.cos x * (∑' k : ℕ, auxPderiv_term (Real.sin x) k)) = 1 := by
    have h1 : Real.cos x * (Real.cos x * (∑' k : ℕ, auxPderiv_term (Real.sin x) k)) =
        (Real.cos x ^ 2) * (∑' k : ℕ, auxPderiv_term (Real.sin x) k) := by ring
    rw [h1, hcos]
    have hPeq : auxP (Real.sin x) = ∑' k : ℕ, auxP_term (Real.sin x) k := rfl
    rw [hPeq]
    linear_combination hode
  rw [hval] at hmul
  exact hmul

theorem auxK_eq {x : ℝ} (hx : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    auxK x = x := by
  have hDderiv : ∀ y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
      HasDerivAt (fun y => auxK y - y) 0 y := by
    intro y hy
    have h := (auxK_hasDerivAt hy).sub (hasDerivAt_id y)
    simp only [sub_self] at h
    exact h
  have hDcont : ∀ y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
      ContinuousAt (fun y => auxK y - y) y := fun y hy => (hDderiv y hy).continuousAt
  by_cases hx0 : x = 0
  · subst hx0
    exact auxK_zero
  · rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · have hIcc_sub : Set.Icc x 0 ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        intro y hy
        have hy1 : x ≤ y := (Set.mem_Icc.mp hy).1
        have hy2 : y ≤ 0 := (Set.mem_Icc.mp hy).2
        have hx1 : -(Real.pi / 2) < x := (Set.mem_Ioo.mp hx).1
        have hx2 : x < Real.pi / 2 := (Set.mem_Ioo.mp hx).2
        constructor <;> linarith [Real.pi_pos]
      have hcont : ContinuousOn (fun y => auxK y - y) (Set.Icc x 0) := by
        intro y hy
        exact (hDcont y (hIcc_sub hy)).continuousWithinAt
      have hderiv : ∀ y ∈ Set.Ioo x 0, HasDerivAt (fun y => auxK y - y) 0 y := by
        intro y hy
        have hyIcc : y ∈ Set.Icc x 0 :=
          ⟨le_of_lt (Set.mem_Ioo.mp hy).1, le_of_lt (Set.mem_Ioo.mp hy).2⟩
        exact hDderiv y (hIcc_sub hyIcc)
      obtain ⟨c, _, hc⟩ :=
        exists_hasDerivAt_eq_slope (fun y => auxK y - y) (fun _ => 0) hneg hcont hderiv
      rw [auxK_zero, sub_self (0 : ℝ), zero_sub (auxK x - x)] at hc
      have hne : (0 : ℝ) - x ≠ 0 := ne_of_gt (by linarith)
      have h0 : (-(auxK x - x)) / (0 - x) = 0 := hc.symm
      rw [div_eq_zero_iff] at h0
      have hnum : -(auxK x - x) = 0 := h0.resolve_right hne
      have hDx : auxK x - x = 0 := neg_eq_zero.mp hnum
      exact sub_eq_zero.mp hDx
    · have hIcc_sub : Set.Icc 0 x ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        intro y hy
        have hy1 : 0 ≤ y := (Set.mem_Icc.mp hy).1
        have hy2 : y ≤ x := (Set.mem_Icc.mp hy).2
        have hx1 : -(Real.pi / 2) < x := (Set.mem_Ioo.mp hx).1
        have hx2 : x < Real.pi / 2 := (Set.mem_Ioo.mp hx).2
        constructor <;> linarith [Real.pi_pos]
      have hcont : ContinuousOn (fun y => auxK y - y) (Set.Icc 0 x) := by
        intro y hy
        exact (hDcont y (hIcc_sub hy)).continuousWithinAt
      have hderiv : ∀ y ∈ Set.Ioo 0 x, HasDerivAt (fun y => auxK y - y) 0 y := by
        intro y hy
        have hyIcc : y ∈ Set.Icc 0 x :=
          ⟨le_of_lt (Set.mem_Ioo.mp hy).1, le_of_lt (Set.mem_Ioo.mp hy).2⟩
        exact hDderiv y (hIcc_sub hyIcc)
      obtain ⟨c, _, hc⟩ :=
        exists_hasDerivAt_eq_slope (fun y => auxK y - y) (fun _ => 0) hpos hcont hderiv
      rw [auxK_zero, sub_self (0 : ℝ), sub_zero (auxK x - x)] at hc
      have hne : (x : ℝ) - 0 ≠ 0 := ne_of_gt (by linarith)
      have h0 : (auxK x - x) / (x - 0) = 0 := hc.symm
      rw [div_eq_zero_iff] at h0
      have hnum : auxK x - x = 0 := h0.resolve_right hne
      exact sub_eq_zero.mp hnum

theorem aux_sin_abs_le_sin_c {c : ℝ} (hc0 : 0 < c) (hc1 : c < Real.pi / 2)
    {y : ℝ} (hy : y ∈ Set.Ioo (-c) c) : |Real.sin y| ≤ Real.sin c := by
  have hyabs : |y| < c := abs_lt.mpr (Set.mem_Ioo.mp hy)
  have hyle : |y| ≤ c := le_of_lt hyabs
  have hpi : |y| ≤ Real.pi := by
    have h1 : |y| < Real.pi / 2 := lt_of_lt_of_le hyabs (le_of_lt hc1)
    linarith [Real.pi_pos]
  have heq : |Real.sin y| = Real.sin |y| := Real.abs_sin_eq_sin_abs_of_abs_le_pi hpi
  rw [heq]
  have h1 : -(Real.pi / 2) ≤ |y| := by
    have hnn : (0 : ℝ) ≤ |y| := abs_nonneg _
    linarith [Real.pi_pos]
  have h2 : c ≤ Real.pi / 2 := le_of_lt hc1
  exact Real.sin_le_sin_of_le_of_le_pi_div_two h1 h2 hyle

theorem aux_sin_c_bounds {c : ℝ} (hc0 : 0 < c) (hc1 : c < Real.pi / 2) :
    0 ≤ Real.sin c ∧ Real.sin c < 1 := by
  have hpos : 0 < Real.sin c := by
    have hlt : c < Real.pi := by linarith [Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi hc0 hlt
  have hlt1 : Real.sin c < 1 := by
    have hle1 : -(Real.pi / 2) ≤ c := by linarith [Real.pi_pos, hc0]
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two hle1 (le_refl _) hc1
    rwa [Real.sin_pi_div_two] at h
  exact ⟨le_of_lt hpos, hlt1⟩

end
end Entry20Piseries1
end Ramanujan.Part1Ch9
end
