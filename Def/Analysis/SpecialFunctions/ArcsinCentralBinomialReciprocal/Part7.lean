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
import Theorem.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal.Part5


namespace MetaMathlibExt

noncomputable def H2fun (x : ℝ) : ℝ :=
  6 * x * Real.arcsin x / (Real.sqrt (1 - x ^ 2)) ^ 5 + (4 + 2 * x ^ 2) / (1 - x ^ 2) ^ 2

end MetaMathlibExt
