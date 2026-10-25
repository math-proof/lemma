import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finset.Max
import Instance.Algebra.BigOperators.Reduced.Part2


/-- Maximum along the last axis: a vector `α → ℝ` reduces to a scalar, a matrix `α → β → ℝ` to a vector. -/
class Function.ReduceMax (γ : Type*) (δ : outParam (Type*)) where
  reduce : γ → δ

