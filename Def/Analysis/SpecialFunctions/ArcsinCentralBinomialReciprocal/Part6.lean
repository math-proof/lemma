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
public import Theorem.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal.Part4

@[expose] public section

namespace MetaMathlibExt

noncomputable def H1fun (x : ℝ) : ℝ :=
  2 * Real.arcsin x / (Real.sqrt (1 - x ^ 2)) ^ 3 + 2 * x / (1 - x ^ 2)

end MetaMathlibExt
