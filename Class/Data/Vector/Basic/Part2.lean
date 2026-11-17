module

public import Mathlib.Data.Vector.MapLemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Theorem.Algebra.Power.Part2
public section

open Nat Lean
open scoped BigOperators

/-- Outer product typeclass: `a ⊗ᵒ b` is the matrix `(i, j) ↦ a i * b j`. -/
class OuterProd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  outer : α → β → γ

