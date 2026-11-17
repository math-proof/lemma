/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/EulerMaclaurinFormula.lean -/

module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators


namespace MetaMathlibExt

/-- Bernoulli kernel on the unit interval starting at `c`: `B_m(x - c) / m!`. -/
noncomputable def emKernel (c : ℤ) (m : ℕ) (x : ℝ) : ℝ :=
  bernoulliFun m (x - (c : ℝ)) / (Nat.factorial m : ℝ)

end MetaMathlibExt
