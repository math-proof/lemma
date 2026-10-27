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
import Theorem.Data.Vector.Basic
open Nat Lean
open scoped BigOperators


/-- Outer product of two vectors: `(a @ᵒ b) i j = a i * b j`, i.e. `a @ᵒ b = Matrix.vecMulVec a b`. -/
instance [Mul α] : OuterProd (m → α) (n → α) (Matrix m n α) where
  outer := Matrix.vecMulVec

