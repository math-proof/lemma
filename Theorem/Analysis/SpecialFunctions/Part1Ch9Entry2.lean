/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Instances.AddCircle.Defs
import Def.Analysis.SpecialFunctions.Part1Ch9Entry2
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry2

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem summable_chapter9Entry2ConstantTerm (s : ℕ) (a : ℝ) (hs : 2 ≤ s) :
    Summable (chapter9Entry2ConstantTerm s a) := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, |a| < K := exists_nat_gt |a|
  have hmajor : Summable (fun k : ℕ => (2 : ℝ) * ((((k : ℝ) + 1) ^ s)⁻¹)) := by
    have hps : Summable (fun n : ℕ => ((((n : ℝ)) ^ s))⁻¹) :=
      (Real.summable_nat_pow_inv (p := s)).mpr (by omega)
    have hshift : Summable (fun n : ℕ => (((((n + 1 : ℕ)) : ℝ) ^ s))⁻¹) := by
      have h := (summable_nat_add_iff 1).mpr hps
      simpa using h
    have hshift' : Summable (fun n : ℕ => (((((n : ℝ)) + 1) ^ s))⁻¹) := by
      simpa using hshift
    exact hshift'.mul_left 2
  apply Summable.of_norm_bounded_eventually hmajor
  have hev : ∀ᶠ k : ℕ in Filter.cofinite, K ≤ k := by
    rw [Filter.eventually_cofinite]
    have hset : {k : ℕ | ¬ K ≤ k} = Set.Iio K := by ext k; simp [Set.mem_Iio, not_le]
    rw [hset]
    exact Set.finite_Iio K
  filter_upwards [hev] with k hk
  set u : ℝ := (((2 * k + 1 : ℕ)) : ℝ) with hu_def
  have hu_eq : u = 2 * (k : ℝ) + 1 := by rw [hu_def]; push_cast; ring
  have hu_nonneg : (0 : ℝ) ≤ u := by rw [hu_eq]; positivity
  have hka : |a| ≤ (k : ℝ) := le_trans (le_of_lt hK) (by exact_mod_cast hk)
  have hbase : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlow : (k : ℝ) + 1 ≤ |u - a| := by
    have h1 : u - |a| ≤ |u - a| := by
      have h2 : |u| - |a| ≤ |u - a| :=
        le_trans (le_abs_self _) (abs_abs_sub_abs_le_abs_sub u a)
      rwa [abs_of_nonneg hu_nonneg] at h2
    linarith
  have hlow2 : (k : ℝ) + 1 ≤ |u + a| := by
    have h1 : u - |a| ≤ |u + a| := by
      have h2 : |u| - |-a| ≤ |u - -a| :=
        le_trans (le_abs_self _) (abs_abs_sub_abs_le_abs_sub u (-a))
      rw [abs_neg, abs_of_nonneg hu_nonneg] at h2
      simpa using h2
    linarith
  have hp1 : ((k : ℝ) + 1) ^ s ≤ |u - a| ^ s := pow_le_pow_left₀ (le_of_lt hbase) hlow s
  have hp2 : ((k : ℝ) + 1) ^ s ≤ |u + a| ^ s := pow_le_pow_left₀ (le_of_lt hbase) hlow2 s
  have hunfold : chapter9Entry2ConstantTerm s a k
      = 1 / (u - a) ^ s + 1 / (u + a) ^ s := by
    unfold chapter9Entry2ConstantTerm
    rw [hu_def]
  have e1 : ‖(1 : ℝ) / (u - a) ^ s‖ = 1 / |u - a| ^ s := by
    rw [norm_div, norm_one, norm_pow, Real.norm_eq_abs]
  have e2 : ‖(1 : ℝ) / (u + a) ^ s‖ = 1 / |u + a| ^ s := by
    rw [norm_div, norm_one, norm_pow, Real.norm_eq_abs]
  rw [hunfold]
  calc ‖(1 : ℝ) / (u - a) ^ s + 1 / (u + a) ^ s‖
        ≤ ‖(1 : ℝ) / (u - a) ^ s‖ + ‖(1 : ℝ) / (u + a) ^ s‖ := norm_add_le _ _
      _ = 1 / |u - a| ^ s + 1 / |u + a| ^ s := by rw [e1, e2]
      _ ≤ 1 / ((k : ℝ) + 1) ^ s + 1 / ((k : ℝ) + 1) ^ s :=
          add_le_add (one_div_le_one_div_of_le (by positivity) hp1)
            (one_div_le_one_div_of_le (by positivity) hp2)
      _ = 2 * ((((k : ℝ) + 1) ^ s)⁻¹) := by rw [one_div]; ring

theorem sub_ne_zero_of_ha (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
    (k : ℕ) : (((2 * k + 1 : ℕ) : ℝ) - a) ≠ 0 := by
  intro h
  have ha0 : a = (((2 * k + 1 : ℕ) : ℝ)) := by linarith
  have hcast : ((((2 * (k : ℤ) + 1 : ℤ)) : ℝ)) = (((2 * k + 1 : ℕ) : ℝ)) := by
    push_cast
    ring
  have hEq : a = ((((2 * (k : ℤ) + 1 : ℤ)) : ℝ)) := by
    rw [hcast]
    exact ha0
  exact ha (k : ℤ) hEq

theorem add_ne_zero_of_ha (a : ℝ) (ha : ∀ z : ℤ, a ≠ ((2 * z + 1 : ℤ) : ℝ))
    (k : ℕ) : (((2 * k + 1 : ℕ) : ℝ) + a) ≠ 0 := by
  intro h
  have ha0 : a = -(((2 * k + 1 : ℕ) : ℝ)) := by linarith
  have hcast : ((((2 * (-(k : ℤ) - 1) + 1 : ℤ)) : ℝ)) = -(((2 * k + 1 : ℕ) : ℝ)) := by
    push_cast
    ring
  have hEq : a = ((((2 * (-(k : ℤ) - 1) + 1 : ℤ)) : ℝ)) := by
    rw [hcast]
    exact ha0
  exact ha (-(k : ℤ) - 1) hEq

end
end Entry2
end Ramanujan.Part1Ch9
end
