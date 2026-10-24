/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/Dilworth.lean -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Antichain
import Mathlib.Order.Lattice.Nat

section
namespace MathlibExt.Combinatorics.Order.DilworthWanted

/-!
# Dilworth's decomposition theorem

In a finite partial order, the largest antichain has as many elements as the fewest chains
covering the order: `maxAntichainSize α = minChainCoverSize α`.
-/

/-- `C` is a finite family of chains whose union is the whole type. -/
def IsChainCoverFin {α : Type*} [PartialOrder α] (C : Finset (Finset α)) : Prop :=
  (∀ s ∈ C, IsChain (· ≤ ·) (s : Set α)) ∧ ∀ a : α, ∃ s ∈ C, a ∈ s

open Classical in
/-- The largest cardinality of an antichain in the finite partial order `α`. -/
noncomputable def maxAntichainSize
    (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  ((Finset.univ : Finset α).powerset).sup fun s =>
    if IsAntichain (· ≤ ·) (s : Set α) then s.card else 0

open Classical in
/-- The smallest number of chains covering the finite partial order `α`. -/
noncomputable def minChainCoverSize
    (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  let all : Finset (Finset (Finset α)) := (Finset.univ.powerset).powerset
  let valid := all.filter fun C => IsChainCoverFin (α := α) C
  if h : valid.Nonempty then valid.inf' h fun C => C.card else 0

-- Helper: width of a finite sub-collection, relativized to a finset.
open Classical in
private noncomputable def widthFin {α : Type*} [Fintype α] [PartialOrder α]
    (s : Finset α) : ℕ :=
  (s.powerset).sup fun t =>
    if IsAntichain (· ≤ ·) (t : Set α) then t.card else 0

-- Helper: chain cover of a finset `s` (chains lie inside `s`).
private def IsChainCoverOf {α : Type*} [PartialOrder α] (s : Finset α)
    (C : Finset (Finset α)) : Prop :=
  (∀ t ∈ C, t ⊆ s) ∧ (∀ t ∈ C, IsChain (· ≤ ·) (t : Set α)) ∧ ∀ a ∈ s, ∃ t ∈ C, a ∈ t

-- Minimal / maximal elements of a finset, and the up/down sets of an antichain.
open Classical in
private noncomputable def minSetOf {α : Type*} [PartialOrder α]
    (s : Finset α) : Finset α :=
  s.filter fun a => ∀ b ∈ s, b ≤ a → a ≤ b

open Classical in
private noncomputable def maxSetOf {α : Type*} [PartialOrder α]
    (s : Finset α) : Finset α :=
  s.filter fun a => ∀ b ∈ s, a ≤ b → b ≤ a

open Classical in
private noncomputable def upSetOf {α : Type*} [PartialOrder α]
    (s A : Finset α) : Finset α :=
  s.filter fun x => ∃ a ∈ A, a ≤ x

open Classical in
private noncomputable def downSetOf {α : Type*} [PartialOrder α]
    (s A : Finset α) : Finset α :=
  s.filter fun x => ∃ a ∈ A, x ≤ a
end MathlibExt.Combinatorics.Order.DilworthWanted
