module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Syntax.Probability.Expectation.Elab
public import Def.Data.List.List.Basic
public import Instance.Analysis.Real.Numbers
public import Notation.Fun
@[expose] public section

open MeasureTheory
open scoped ENNReal.ToRealCoe


/-- The type of the vector `x[a:b]` of values `Fin (b - a) → α`, as it appears in the type of the random
vector `x[a:b] : Ω → FunSlice.Vec α ⟨a, b, 1⟩`. -/
abbrev FunSlice.Vec (α : Type*) (s : Slice) : Type _ :=
  Fin (s.stop.toNat - s.start.toNat) → α

