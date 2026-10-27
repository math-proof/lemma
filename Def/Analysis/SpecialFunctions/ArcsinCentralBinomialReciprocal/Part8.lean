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
import Theorem.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal.Part6


namespace MetaMathlibExt

noncomputable def Jfun (y : ℝ) : ℝ :=
  (Dfun y - H1fun y) * (Real.sqrt (1 - y ^ 2)) ^ 3

end MetaMathlibExt
