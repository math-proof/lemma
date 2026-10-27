/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Def.Analysis.SpecialFunctions.CatalanConstantProducts.Part4


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
