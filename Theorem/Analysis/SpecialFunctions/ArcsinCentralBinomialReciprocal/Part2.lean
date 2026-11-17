module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Def.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal.Part3

public section

namespace MetaMathlibExt

theorem dcoef_nonneg (n : ℕ) : 0 ≤ dcoef n := by
  unfold dcoef
  apply div_nonneg (pow_nonneg (by norm_num) n)
  exact le_of_lt (choose_pos' n)

theorem dcoef_rec (n : ℕ) :
    (2 * (n : ℝ) + 1) * dcoef (n + 1) = 2 * ((n : ℝ) + 1) * dcoef n := by
  have hr := choose_rec n
  have hC0 : (Nat.choose (2 * n) n : ℝ) ≠ 0 := choose_ne' n
  have hC1 : (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) ≠ 0 := choose_ne' (n + 1)
  have h4 : (4 ^ (n + 1) : ℝ) = 4 * 4 ^ n := by rw [pow_succ]; ring
  have e : (2 * (n : ℝ) + 1) * (4 * 4 ^ n) * (Nat.choose (2 * n) n : ℝ)
      = (2 * ((n : ℝ) + 1) * 4 ^ n) * (Nat.choose (2 * (n + 1)) (n + 1) : ℝ) := by
    linear_combination (-2 * 4 ^ n) * hr
  simp only [dcoef, h4, ← mul_div_assoc]
  rw [div_eq_div_iff hC1 hC0]
  linear_combination e

theorem dcoef_one : dcoef 1 = 2 := by
  have h : Nat.choose (2 * 1) 1 = 2 := by decide
  norm_num [dcoef, h]

end MetaMathlibExt
