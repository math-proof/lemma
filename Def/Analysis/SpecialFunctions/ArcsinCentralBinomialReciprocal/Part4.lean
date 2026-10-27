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
import Theorem.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal.Part2


namespace MetaMathlibExt

noncomputable def Dterm (x : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else 2 * dcoef n * x ^ (2 * n - 1)

end MetaMathlibExt
