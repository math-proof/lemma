module

public import Mathlib.Data.Vector.MapLemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Theorem.Nat.EqMin_SubMulS
public import Theorem.Nat.EqAddMulDiv
public import Theorem.List.Prod.eq.MulProdS
public import Theorem.Algebra.Power.Part2
public import Class.Data.Vector.Basic.Part2

open Nat Lean
open scoped BigOperators


@[expose] public section

/-- Outer product of two vectors: `(a ⊗ᵒ b) i j = a i * b j`, i.e. `a ⊗ᵒ b = Matrix.vecMulVec a b`. -/
instance [Mul α] : OuterProd (m → α) (n → α) (Matrix m n α) where
  outer := Matrix.vecMulVec

