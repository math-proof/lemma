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
import Def.Analysis.SpecialFunctions.Part1Ch9Entry20Piseries1.Part3
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

theorem auxP_summable {s : ℝ} (hs : |s| < 1) :
    Summable (auxP_term s) := by
  have hr : |(|s| ^ 2)| < 1 := by
    have hsq : |s| ^ 2 < 1 := by nlinarith [hs, abs_nonneg s]
    have hnn : (0 : ℝ) ≤ |s| ^ 2 := by positivity
    rwa [abs_of_nonneg hnn]
  have hgeo : Summable (fun k : ℕ => (|s| ^ 2) ^ k) :=
    summable_geometric_of_abs_lt_one hr
  have hbound : Summable (fun k : ℕ => |s| * (|s| ^ 2) ^ k) := hgeo.mul_left |s|
  apply Summable.of_norm_bounded hbound
  intro k
  have hA : ‖auxA k‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (auxA_nonneg k)]
    exact auxA_le_one k
  have hpow : (‖s ^ (2 * k + 1)‖) = |s| * (|s| ^ 2) ^ k := by
    rw [norm_pow, Real.norm_eq_abs]
    have e : |s| ^ (2 * k + 1) = |s| * (|s| ^ 2) ^ k := by
      rw [pow_succ, ← pow_mul, mul_comm]
    exact e
  calc ‖auxP_term s k‖ = ‖auxA k‖ * ‖s ^ (2 * k + 1)‖ := by
        unfold auxP_term
        rw [norm_mul]
    _ ≤ 1 * (|s| * (|s| ^ 2) ^ k) := by
        rw [hpow]
        exact mul_le_mul hA le_rfl (by positivity) (by positivity)
    _ = |s| * (|s| ^ 2) ^ k := one_mul _

theorem auxPderiv_bound_summable {rho : ℝ} (h0 : 0 ≤ rho) (h1 : rho < 1) :
    Summable (fun k : ℕ => ((((2 * k + 1 : ℕ)) : ℝ)) * rho ^ (2 * k)) := by
  have hr1 : |rho ^ 2| < 1 := by
    have hsq : rho ^ 2 < 1 := by nlinarith [h0, h1, sq_nonneg rho]
    have hnn : (0 : ℝ) ≤ rho ^ 2 := by positivity
    rwa [abs_of_nonneg hnn]
  have hgeo : Summable (fun k : ℕ => (rho ^ 2) ^ k) :=
    summable_geometric_of_abs_lt_one hr1
  have hnorm : ‖rho ^ 2‖ < 1 := by
    rwa [Real.norm_eq_abs]
  have hpow1 : Summable (fun k : ℕ => (k : ℝ) * (rho ^ 2) ^ k) := by
    simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have h2k : Summable (fun k : ℕ => 2 * (k : ℝ) * (rho ^ 2) ^ k) := by
    have h := hpow1.mul_left 2
    have heq : (fun k : ℕ => 2 * ((k : ℝ) * (rho ^ 2) ^ k)) =
        (fun k : ℕ => 2 * (k : ℝ) * (rho ^ 2) ^ k) := by
      funext k
      ring
    rwa [heq] at h
  have hsum : Summable (fun k : ℕ => 2 * (k : ℝ) * (rho ^ 2) ^ k + (rho ^ 2) ^ k) :=
    h2k.add hgeo
  have heq : (fun k : ℕ => ((((2 * k + 1 : ℕ)) : ℝ)) * rho ^ (2 * k)) =
      (fun k : ℕ => 2 * (k : ℝ) * (rho ^ 2) ^ k + (rho ^ 2) ^ k) := by
    funext k
    have hcast : ((((2 * k + 1 : ℕ)) : ℝ)) = 2 * (k : ℝ) + 1 := by
      push_cast
      ring
    have hpow : rho ^ (2 * k) = (rho ^ 2) ^ k := by
      rw [← pow_mul]
    rw [hcast, hpow]
    ring
  rw [heq]
  exact hsum

theorem auxP_hasDerivAt {s : ℝ} (hs : |s| < 1) :
    HasDerivAt auxP (∑' k : ℕ, auxPderiv_term s k) s := by
  set rho : ℝ := (|s| + 1) / 2 with hrhodef
  have hrho0 : 0 ≤ rho := by
    unfold rho
    have h : (0 : ℝ) ≤ |s| + 1 := by
      have hnn : (0 : ℝ) ≤ |s| := abs_nonneg _
      linarith
    linarith
  have hrho1 : rho < 1 := by
    unfold rho
    linarith
  have hsmem : s ∈ Set.Ioo (-rho) rho := by
    have hlt : |s| < rho := by
      unfold rho
      linarith
    exact Set.mem_Ioo.mpr (abs_lt.mp hlt)
  have hu : Summable (fun k : ℕ => ((((2 * k + 1 : ℕ)) : ℝ)) * rho ^ (2 * k)) :=
    auxPderiv_bound_summable hrho0 hrho1
  have hterm : ∀ k : ℕ, ∀ y ∈ Set.Ioo (-rho) rho,
      HasDerivAt (fun y => auxP_term y k) (auxPderiv_term y k) y := by
    intro k y _
    unfold auxP_term auxPderiv_term
    have hpow : HasDerivAt (fun y : ℝ => y ^ (2 * k + 1))
        ((((2 * k + 1 : ℕ)) : ℝ) * y ^ (2 * k + 1 - 1)) y :=
      hasDerivAt_pow (2 * k + 1) y
    have hsub : 2 * k + 1 - 1 = 2 * k := Nat.add_sub_cancel _ _
    rw [hsub] at hpow
    have hmul := hpow.const_mul (auxA k)
    have heq : auxA k * ((((2 * k + 1 : ℕ)) : ℝ) * y ^ (2 * k)) =
        auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * y ^ (2 * k) := by ring
    rw [heq] at hmul
    exact hmul
  have hbound : ∀ k : ℕ, ∀ y ∈ Set.Ioo (-rho) rho,
      ‖auxPderiv_term y k‖ ≤ ((((2 * k + 1 : ℕ)) : ℝ)) * rho ^ (2 * k) := by
    intro k y hy
    have hyabs : |y| < rho := abs_lt.mpr (Set.mem_Ioo.mp hy)
    have hyle : |y| ≤ rho := le_of_lt hyabs
    have hA : ‖auxA k‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (auxA_nonneg k)]
      exact auxA_le_one k
    have hnn1 : (0 : ℝ) ≤ ((((2 * k + 1 : ℕ)) : ℝ)) := Nat.cast_nonneg _
    have hpow_le : |y| ^ (2 * k) ≤ rho ^ (2 * k) :=
      pow_le_pow_left₀ (abs_nonneg _) hyle _
    unfold auxPderiv_term
    rw [norm_mul, norm_mul, norm_pow, Real.norm_eq_abs]
    have h2 : ‖((((2 * k + 1 : ℕ)) : ℝ))‖ = ((((2 * k + 1 : ℕ)) : ℝ)) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnn1]
    rw [h2]
    calc ‖auxA k‖ * ((((2 * k + 1 : ℕ)) : ℝ)) * |y| ^ (2 * k)
        ≤ 1 * ((((2 * k + 1 : ℕ)) : ℝ)) * rho ^ (2 * k) := by
          apply mul_le_mul _ hpow_le (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hA hnn1
      _ = ((((2 * k + 1 : ℕ)) : ℝ)) * rho ^ (2 * k) := by ring
  have hmain := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
    (convex_Ioo (-rho) rho).isPreconnected hterm hbound hsmem
    (auxP_summable hs) hsmem
  have efun : (fun z => ∑' k : ℕ, auxP_term z k) = auxP := by
    funext z
    rfl
  rw [efun] at hmain
  exact hmain

theorem auxPderiv_summable {s : ℝ} (hs : |s| < 1) :
    Summable (auxPderiv_term s) := by
  have hbound : Summable (fun k : ℕ => ((((2 * k + 1 : ℕ)) : ℝ)) * |s| ^ (2 * k)) :=
    auxPderiv_bound_summable (abs_nonneg _) hs
  apply Summable.of_norm_bounded hbound
  intro k
  have hA : ‖auxA k‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (auxA_nonneg k)]
    exact auxA_le_one k
  have hnn1 : (0 : ℝ) ≤ ((((2 * k + 1 : ℕ)) : ℝ)) := Nat.cast_nonneg _
  have h2 : ‖((((2 * k + 1 : ℕ)) : ℝ))‖ = ((((2 * k + 1 : ℕ)) : ℝ)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hnn1]
  have hpow : (‖s ^ (2 * k)‖) = |s| ^ (2 * k) := by
    rw [norm_pow, Real.norm_eq_abs]
  unfold auxPderiv_term
  rw [norm_mul, norm_mul, h2, hpow]
  calc ‖auxA k‖ * ((((2 * k + 1 : ℕ)) : ℝ)) * |s| ^ (2 * k)
      ≤ 1 * ((((2 * k + 1 : ℕ)) : ℝ)) * |s| ^ (2 * k) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hA hnn1
    _ = ((((2 * k + 1 : ℕ)) : ℝ)) * |s| ^ (2 * k) := by ring

theorem auxP_ode {s : ℝ} (hs : |s| < 1) :
    (1 - s ^ 2) * (∑' k : ℕ, auxPderiv_term s k) - s * (∑' k : ℕ, auxP_term s k) = 1 := by
  have hf : Summable (auxPderiv_term s) := auxPderiv_summable hs
  have hp : Summable (auxP_term s) := auxP_summable hs
  have hg : Summable (fun k : ℕ => auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k + 2)) := by
    have h := hf.mul_right (s ^ 2)
    have heq : (fun k : ℕ => auxPderiv_term s k * s ^ 2) =
        (fun k : ℕ => auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k + 2)) := by
      funext k
      unfold auxPderiv_term
      have e : s ^ (2 * k) * s ^ 2 = s ^ (2 * k + 2) := by
        rw [← pow_add]
      calc auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k) * s ^ 2
          = auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * (s ^ (2 * k) * s ^ 2) := by ring
        _ = auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k + 2) := by rw [e]
    rwa [heq] at h
  have hh : Summable (fun k : ℕ => auxA k * s ^ (2 * k + 2)) := by
    have h := hp.mul_right s
    have heq : (fun k : ℕ => auxP_term s k * s) =
        (fun k : ℕ => auxA k * s ^ (2 * k + 2)) := by
      funext k
      unfold auxP_term
      have e : s ^ (2 * k + 1) * s = s ^ (2 * k + 2) := by
        have h2 : 2 * k + 2 = (2 * k + 1) + 1 := by omega
        rw [h2]
        exact (pow_succ s _).symm
      calc auxA k * s ^ (2 * k + 1) * s
          = auxA k * (s ^ (2 * k + 1) * s) := by ring
        _ = auxA k * s ^ (2 * k + 2) := by rw [e]
    rwa [heq] at h
  have hj : Summable (fun k : ℕ => auxA k * ((((2 * k + 2 : ℕ)) : ℝ)) * s ^ (2 * k + 2)) := by
    have h := hg.add hh
    have heq : (fun k : ℕ => auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k + 2) +
        auxA k * s ^ (2 * k + 2)) =
        (fun k : ℕ => auxA k * ((((2 * k + 2 : ℕ)) : ℝ)) * s ^ (2 * k + 2)) := by
      funext k
      have hcast : ((((2 * k + 2 : ℕ)) : ℝ)) = ((((2 * k + 1 : ℕ)) : ℝ)) + 1 := by
        have h2 : (2 * k + 2 : ℕ) = (2 * k + 1) + 1 := by omega
        rw [h2]
        push_cast
        ring
      rw [hcast]
      ring
    rwa [heq] at h
  have hs2 : s ^ 2 * (∑' k : ℕ, auxPderiv_term s k) =
      ∑' k : ℕ, (auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k + 2)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    unfold auxPderiv_term
    have e : s ^ 2 * s ^ (2 * k) = s ^ (2 * k + 2) := by
      have h2 : 2 + 2 * k = 2 * k + 2 := by ring
      calc s ^ 2 * s ^ (2 * k) = s ^ (2 + 2 * k) := by rw [← pow_add]
        _ = s ^ (2 * k + 2) := by rw [h2]
    calc s ^ 2 * (auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k))
        = auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * (s ^ 2 * s ^ (2 * k)) := by ring
      _ = auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k + 2) := by rw [e]
  have hsp : s * (∑' k : ℕ, auxP_term s k) =
      ∑' k : ℕ, (auxA k * s ^ (2 * k + 2)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    unfold auxP_term
    have e : s * s ^ (2 * k + 1) = s ^ (2 * k + 2) := by
      have h2 : 2 * k + 2 = (2 * k + 1) + 1 := by omega
      calc s * s ^ (2 * k + 1) = s ^ (2 * k + 1) * s := by ring
        _ = s ^ ((2 * k + 1) + 1) := (pow_succ s _).symm
        _ = s ^ (2 * k + 2) := by rw [← h2]
    calc s * (auxA k * s ^ (2 * k + 1))
        = auxA k * (s * s ^ (2 * k + 1)) := by ring
      _ = auxA k * s ^ (2 * k + 2) := by rw [e]
  have hgh : (∑' k : ℕ, (auxA k * ((((2 * k + 2 : ℕ)) : ℝ)) * s ^ (2 * k + 2))) =
      (∑' k : ℕ, (auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k + 2))) +
        ∑' k : ℕ, (auxA k * s ^ (2 * k + 2)) := by
    have h := hg.tsum_add hh
    have heq : (fun k : ℕ => auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k + 2) +
        auxA k * s ^ (2 * k + 2)) =
        (fun k : ℕ => auxA k * ((((2 * k + 2 : ℕ)) : ℝ)) * s ^ (2 * k + 2)) := by
      funext k
      have hcast : ((((2 * k + 2 : ℕ)) : ℝ)) = ((((2 * k + 1 : ℕ)) : ℝ)) + 1 := by
        have h2 : (2 * k + 2 : ℕ) = (2 * k + 1) + 1 := by omega
        rw [h2]
        push_cast
        ring
      rw [hcast]
      ring
    rw [← heq, h]
  have hf0 : auxPderiv_term s 0 = 1 := by
    unfold auxPderiv_term
    rw [auxA_zero]
    norm_num
  have hshift := hf.tsum_eq_zero_add
  rw [hf0] at hshift
  have htail : (∑' k : ℕ, auxPderiv_term s (k + 1)) =
      ∑' k : ℕ, (auxA k * ((((2 * k + 2 : ℕ)) : ℝ)) * s ^ (2 * k + 2)) := by
    apply tsum_congr
    intro k
    unfold auxPderiv_term
    have hn : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    have hcast : ((((2 * (k + 1) + 1 : ℕ)) : ℝ)) = ((((2 * k + 3 : ℕ)) : ℝ)) := by
      rw [hn]
    have hexp : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [hcast, hexp]
    have hrec := auxA_rec k
    calc auxA (k + 1) * ((((2 * k + 3 : ℕ)) : ℝ)) * s ^ (2 * k + 2)
        = ((((2 * k + 3 : ℕ)) : ℝ)) * auxA (k + 1) * s ^ (2 * k + 2) := by ring
      _ = ((((2 * k + 2 : ℕ)) : ℝ)) * auxA k * s ^ (2 * k + 2) := by rw [hrec]
      _ = auxA k * ((((2 * k + 2 : ℕ)) : ℝ)) * s ^ (2 * k + 2) := by ring
  rw [htail] at hshift
  calc (1 - s ^ 2) * (∑' k : ℕ, auxPderiv_term s k) - s * (∑' k : ℕ, auxP_term s k)
      = (∑' k : ℕ, auxPderiv_term s k) - s ^ 2 * (∑' k : ℕ, auxPderiv_term s k) -
        s * (∑' k : ℕ, auxP_term s k) := by ring
    _ = (∑' k : ℕ, auxPderiv_term s k) -
        (∑' k : ℕ, (auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k + 2)) +
          ∑' k : ℕ, (auxA k * s ^ (2 * k + 2))) := by
        rw [hs2, hsp]
        ring
    _ = (∑' k : ℕ, auxPderiv_term s k) -
        ∑' k : ℕ, (auxA k * ((((2 * k + 2 : ℕ)) : ℝ)) * s ^ (2 * k + 2)) := by
        rw [← hgh]
    _ = 1 := by
        rw [hshift]
        ring

theorem aux_sin_abs_lt_one {x : ℝ} (hx : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    |Real.sin x| < 1 := by
  have hx1 : -(Real.pi / 2) < x := (Set.mem_Ioo.mp hx).1
  have hx2 : x < Real.pi / 2 := (Set.mem_Ioo.mp hx).2
  have hle1 : -(Real.pi / 2) ≤ x := le_of_lt hx1
  have hle2 : x ≤ Real.pi / 2 := le_of_lt hx2
  have hupper : Real.sin x < 1 := by
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two hle1 (le_refl _) hx2
    rwa [Real.sin_pi_div_two] at h
  have hlower : (-1 : ℝ) < Real.sin x := by
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two (le_refl _) hle2 hx1
    have hsin : Real.sin (-(Real.pi / 2)) = -1 := by
      rw [Real.sin_neg, Real.sin_pi_div_two]
    rwa [hsin] at h
  exact abs_lt.mpr ⟨hlower, hupper⟩

theorem auxP_zero : auxP 0 = 0 := by
  unfold auxP
  have h0 : ∀ k : ℕ, auxP_term 0 k = 0 := by
    intro k
    unfold auxP_term
    have hne : 2 * k + 1 ≠ 0 := by omega
    rw [zero_pow hne, mul_zero]
  rw [tsum_congr h0]
  exact tsum_zero

end
end Entry20Piseries1
end Ramanujan.Part1Ch9
end
