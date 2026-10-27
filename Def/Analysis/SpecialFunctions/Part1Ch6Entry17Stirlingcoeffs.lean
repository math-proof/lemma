/-
Author: @akiezun, Avocado
-/
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Theorem.Analysis.SpecialFunctions.Part1Ch6Entry17Stirlingcoeffs
open scoped BigOperators
open Filter Finset Topology


-- Diagonal reindexing: pairs (i,j) correspond to (k = i+j+1, i < k).
def diagEquiv : ℕ × ℕ ≃ (k : ℕ) × Fin k where
  toFun p := ⟨p.1 + p.2 + 1, ⟨p.1, by omega⟩⟩
  invFun q := (q.2.val, q.1 - 1 - q.2.val)
  left_inv := by
    rintro ⟨i, j⟩
    change (i, i + j + 1 - 1 - i) = (i, j)
    rw [Prod.mk.injEq]
    exact ⟨rfl, by omega⟩
  right_inv := by
    rintro ⟨k, ⟨i, h⟩⟩
    have e : i + (k - 1 - i) + 1 = k := by omega
    have key : ∀ (A : ℕ) (e' : A = k) (a : Fin A) (_ha : a.val = i),
        (⟨A, a⟩ : (k' : ℕ) × Fin k') = ⟨k, (⟨i, h⟩ : Fin k)⟩ := by
      intro A e' a ha
      subst e'
      have hav : a = ⟨i, h⟩ := by ext; exact ha
      rw [hav]
    exact key _ e _ rfl

