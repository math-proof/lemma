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
import Def.Analysis.SpecialFunctions.CatalanConstantProducts.Part5


section

namespace MetaMathlibExt

theorem ccp_term_den_pos (u : ℝ) (k : ℕ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 < 4 * (((k + 1 : ℕ) : ℝ) ^ 2) - u ^ 2 := by
  have hub : u ^ 2 ≤ 1 := by
    have habs : |u| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    calc
      u ^ 2 = |u| ^ 2 := by rw [sq_abs]
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = 1 := one_pow 2
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_left 1 k
  have hk2 : (1 : ℝ) ≤ (((k + 1 : ℕ) : ℝ) ^ 2) := by
    calc
      (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (((k + 1 : ℕ) : ℝ) ^ 2) := pow_le_pow_left₀ (by norm_num) hk 2
  linarith

theorem ccp_term_nonneg (u : ℝ) (k : ℕ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ ccp_term u k := by
  unfold ccp_term
  exact div_nonneg (sq_nonneg u) (ccp_term_den_pos u k hu0 hu1).le

theorem ccp_term_antitone (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Antitone (ccp_term u) := by
  intro k l hkl
  have hcast : ((k + 1 : ℕ) : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hkl 1
  have hsquare : (((k + 1 : ℕ) : ℝ) ^ 2) ≤ (((l + 1 : ℕ) : ℝ) ^ 2) :=
    pow_le_pow_left₀ (by positivity) hcast 2
  unfold ccp_term
  apply div_le_div_of_nonneg_left (sq_nonneg u) (ccp_term_den_pos u k hu0 hu1)
  linarith

end MetaMathlibExt
end
