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
import Instance.Data.Vector.Basic.Part3
open Nat Lean
open scoped BigOperators


@[simp]
theorem FinsetPow.dot_eq [AddCommMonoid α] [HPow α ℕ α] [Mul α]
    (γ : α) (s : Finset ℕ) (g : ℕ → α) :
    (γ ^ s) @ g = ∑ i ∈ s, γ ^ i * g i := rfl

