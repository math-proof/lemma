module

public import Mathlib.Data.Vector.MapLemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Theorem.Algebra.Power.Part2
public section

open Nat Lean
open scoped BigOperators

class Dot (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  dot : α → β → γ

