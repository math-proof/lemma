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
public import Theorem.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal

@[expose] public section

namespace MetaMathlibExt

noncomputable def dcoef (n : ℕ) : ℝ := (4 ^ n : ℝ) / (Nat.choose (2 * n) n : ℝ)

end MetaMathlibExt
