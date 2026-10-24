/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ArcsinCentralBinomialReciprocal.lean -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace MetaMathlibExt

private noncomputable def Aterm (x : ℝ) (n : ℕ) : ℝ :=
  (2*x)^(2*n)/((n : ℝ)*(Nat.choose (2*n) n : ℝ))

private noncomputable def Sfun (x : ℝ) : ℝ := ∑' n, Aterm x n

private noncomputable def dcoef (n : ℕ) : ℝ := (4 ^ n : ℝ) / (Nat.choose (2 * n) n : ℝ)
private noncomputable def Dterm (x : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else 2 * dcoef n * x ^ (2 * n - 1)

private noncomputable def S2term (x : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else 2 * dcoef n * ((2 * n - 1 : ℕ) : ℝ) * x ^ (2 * n - 2)

private noncomputable def Dfun (x : ℝ) : ℝ := ∑' n, Dterm x n
private noncomputable def S2fun (x : ℝ) : ℝ := ∑' n, S2term x n
private noncomputable def Hfun (x : ℝ) : ℝ := (2 * x / Real.sqrt (1 - x ^ 2)) * Real.arcsin x

private noncomputable def H1fun (x : ℝ) : ℝ :=
  2 * Real.arcsin x / (Real.sqrt (1 - x ^ 2)) ^ 3 + 2 * x / (1 - x ^ 2)

private noncomputable def H2fun (x : ℝ) : ℝ :=
  6 * x * Real.arcsin x / (Real.sqrt (1 - x ^ 2)) ^ 5 + (4 + 2 * x ^ 2) / (1 - x ^ 2) ^ 2

private noncomputable def Jfun (y : ℝ) : ℝ :=
  (Dfun y - H1fun y) * (Real.sqrt (1 - y ^ 2)) ^ 3
end MetaMathlibExt
