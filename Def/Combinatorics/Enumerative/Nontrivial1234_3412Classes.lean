/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Relation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Order.Fin.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic


namespace MetaMathlibExt

/-! ## Basic definitions: the move relation, patterns, class counts. -/

/-- The {1234, 3412}-replacement move on permutations of `Fin n`, exactly the
body of the `Wanted` entry's `let`. -/
def ntMove (n : ℕ) : Equiv.Perm (Fin n) → Equiv.Perm (Fin n) → Prop :=
  fun σ τ => ∃ i1 i2 i3 i4 : Fin n,
    i1.val < i2.val ∧ i2.val < i3.val ∧ i3.val < i4.val ∧
      σ i1 < σ i2 ∧ σ i2 < σ i3 ∧ σ i3 < σ i4 ∧
      τ i1 = σ i3 ∧ τ i2 = σ i4 ∧ τ i3 = σ i1 ∧ τ i4 = σ i2 ∧
      ∀ j : Fin n, j ≠ i1 → j ≠ i2 → j ≠ i3 → j ≠ i4 → τ j = σ j

/-- A permutation contains a 1234 or a 3412 pattern. -/
def ntPat (n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  (∃ i1 i2 i3 i4 : Fin n, i1.val < i2.val ∧ i2.val < i3.val ∧ i3.val < i4.val ∧
    σ i1 < σ i2 ∧ σ i2 < σ i3 ∧ σ i3 < σ i4) ∨
  (∃ i1 i2 i3 i4 : Fin n, i1.val < i2.val ∧ i2.val < i3.val ∧ i3.val < i4.val ∧
    σ i3 < σ i4 ∧ σ i4 < σ i1 ∧ σ i1 < σ i2)

/-- A permutation has an increasing subsequence of length five. -/
def ntInc5 (n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∃ a b c d e : Fin n, a.val < b.val ∧ b.val < c.val ∧ c.val < d.val ∧
    d.val < e.val ∧ σ a < σ b ∧ σ b < σ c ∧ σ c < σ d ∧ σ d < σ e

/-- Number of nontrivial `EqvGen r` classes meeting the set `S`. -/
noncomputable def ntncl {α : Type*} (r : α → α → Prop) (S : Set α) : ℕ :=
  Nat.card { C : Set α // ∃ x ∈ S, C = { y | Relation.EqvGen r x y } ∧ 1 < Nat.card ↥C }

/-- The exceptional set: permutations with neither extreme fixed. -/
def ntE (m : ℕ) : Set (Equiv.Perm (Fin (m + 1))) :=
  { σ | σ 0 ≠ Fin.last m ∧ σ (Fin.last m) ≠ 0 }

/-- Even and odd reference permutations. -/
def ntEven (n : ℕ) : Equiv.Perm (Fin n) := 1

def ntOdd (m : ℕ) : Equiv.Perm (Fin (m + 2)) :=
  Equiv.swap ⟨m, by omega⟩ ⟨m + 1, by omega⟩

/-- Reverse-complement of a permutation. -/
def ntRC {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  (Fin.revPerm : Equiv.Perm (Fin n)) * σ * (Fin.revPerm : Equiv.Perm (Fin n))

/-! ## N2: the `EqvGen` class-counting framework. -/

/-- The `EqvGen r` class of `x`, as a set. -/
def ntCls {α : Type*} (r : α → α → Prop) (x : α) : Set α :=
  { y | Relation.EqvGen r x y }

end MetaMathlibExt
