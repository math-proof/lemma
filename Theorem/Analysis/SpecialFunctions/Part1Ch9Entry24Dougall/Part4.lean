/-
Author: @akiezun, Avocado
-/

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
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Def.Analysis.SpecialFunctions.Part1Ch9Entry24Dougall.Part4

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry24Dougall

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

theorem seqT_pos (n : ℕ) : 0 < seqT n := by
  unfold seqT
  have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  exact one_div_pos.mpr hpos

theorem seqT_le_half (n : ℕ) : seqT n ≤ 1 / 2 := by
  unfold seqT
  have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    linarith
  exact one_div_le_one_div_of_le (by norm_num) h2

theorem seqT_lt_one (n : ℕ) : seqT n < 1 := by
  calc seqT n ≤ 1 / 2 := seqT_le_half n
    _ < 1 := by norm_num

theorem tendsto_seqT : Tendsto seqT atTop (𝓝 0) := by
  have htop : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have h0 : Tendsto (fun n : ℕ => (((n : ℝ) + 2)⁻¹ : ℝ)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp htop
  have hfun : seqT = (fun n : ℕ => (((n : ℝ) + 2)⁻¹ : ℝ)) := by
    funext n
    unfold seqT
    rw [one_div]
  rw [hfun]
  exact h0

end
end Entry24Dougall
end Ramanujan.Part1Ch9
end
