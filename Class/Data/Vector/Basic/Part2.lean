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
import Notation.Data.Vector.Basic
open Nat Lean
open scoped BigOperators


/-- Outer product typeclass: `a @ᵒ b` is the matrix `(i, j) ↦ a i * b j`. -/
class OuterProd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  outer : α → β → γ

