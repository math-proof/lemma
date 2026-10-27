import Mathlib.Data.Vector.MapLemmas
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lemma.Nat.EqMin_SubMulS
import Lemma.Nat.EqAddMulDiv
import Lemma.List.LengthRange.eq.Length
import Lemma.List.Prod.eq.MulProdS
import Theorem.Algebra.Power.Part2
import Theorem.Function
import Instance.Data.Vector.Basic.Part4
open Nat Lean
open scoped BigOperators


@[simp]
theorem OuterProd.eq.vecMulVec [Mul α] (a : m → α) (b : n → α) : a @ᵒ b = Matrix.vecMulVec a b :=
  rfl

@[simp]
theorem OuterProd.apply [Mul α] (a : m → α) (b : n → α) (i : m) (j : n) : (a @ᵒ b) i j = a i * b j :=
  rfl

