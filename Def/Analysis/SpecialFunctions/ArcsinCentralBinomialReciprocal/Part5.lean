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
import Theorem.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal.Part3


namespace MetaMathlibExt

noncomputable def S2term (x : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else 2 * dcoef n * ((2 * n - 1 : ℕ) : ℝ) * x ^ (2 * n - 2)

noncomputable def Dfun (x : ℝ) : ℝ := ∑' n, Dterm x n

noncomputable def S2fun (x : ℝ) : ℝ := ∑' n, S2term x n

noncomputable def Hfun (x : ℝ) : ℝ := (2 * x / Real.sqrt (1 - x ^ 2)) * Real.arcsin x

end MetaMathlibExt
