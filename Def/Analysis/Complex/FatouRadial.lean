module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.Analysis.Complex.FatouRadial

@[expose] public section

open MeasureTheory Complex Set Filter Metric
open scoped Topology


namespace Complex.FatouRadialWanted

noncomputable def fatouKernel (r t : ℝ) : ℝ :=
  (1 - r ^ 2) * Real.sin t / (1 - 2 * r * Real.cos t + r ^ 2) ^ 2

end Complex.FatouRadialWanted
