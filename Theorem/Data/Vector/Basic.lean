module
public import Mathlib.Data.Vector.MapLemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Theorem.Nat.EqMin_SubMulS
public import Theorem.Nat.EqAddMulDiv
public import Theorem.List.Prod.eq.MulProdS
public import Theorem.Algebra.Power.Part2
public import Instance.Data.Vector.Basic.Dot
public import Instance.Data.Vector.Basic.OuterProduct
public import Notation.Data.Dot
public import Notation.Data.Vector.Basic.Part2
open Nat Lean
open scoped BigOperators


public section

@[simp]
public theorem FinsetPow.dot_eq [AddCommMonoid α] [HPow α ℕ α] [Mul α]
    (γ : α) (s : Finset ℕ) (g : ℕ → α) :
    (γ ^ s) ⬝ᵥ g = ∑ i ∈ s, γ ^ i * g i := rfl

@[simp]
public theorem OuterProd.eq.vecMulVec [Mul α] (a : m → α) (b : n → α) : a ⊗ᵒ b = Matrix.vecMulVec a b :=
  rfl

@[simp]
public theorem OuterProd.apply [Mul α] (a : m → α) (b : n → α) (i : m) (j : n) : (a ⊗ᵒ b) i j = a i * b j :=
  rfl
