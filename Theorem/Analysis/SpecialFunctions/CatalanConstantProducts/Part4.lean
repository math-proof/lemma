/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Real.Pi.Leibniz
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Def.Analysis.SpecialFunctions.CatalanConstantProducts.Part4

@[expose] public section

section

namespace MetaMathlibExt

/-- Finite sums as range partial sums. -/
theorem catFint_eq_range (N : ℕ) (u : ℝ) :
    catFint N u
      = ∑ k ∈ Finset.range N,
        (-1 : ℝ) ^ k * (u ^ 2 / ((4 * (((k + 1 : ℕ) : ℝ) ^ 2) - u ^ 2))) := by
  unfold catFint
  have hIcc : Finset.Icc 1 N = Finset.Ico 1 (N + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro k hk
  have hpow : (-1 : ℝ) ^ ((1 + k) + 1) = (-1 : ℝ) ^ k := by
    have hexp : (1 + k) + 1 = k + 2 := by ring
    rw [hexp, pow_add]
    norm_num
  have hcast : (((1 + k : ℕ) : ℝ)) = (((k + 1 : ℕ) : ℝ)) := by
    push_cast
    ring
  rw [hpow, hcast]
  ring

end MetaMathlibExt
end
