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
public import Theorem.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal.Part5


public section

namespace MetaMathlibExt

noncomputable def H2fun (x : ℝ) : ℝ :=
  6 * x * Real.arcsin x / (Real.sqrt (1 - x ^ 2)) ^ 5 + (4 + 2 * x ^ 2) / (1 - x ^ 2) ^ 2

end MetaMathlibExt
