/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/FinitePosets.lean -/

import Mathlib.Order.Lattice.Nat
/-!
# Mirsky's theorem

In a finite poset the maximum size of a chain equals the minimum number of antichains covering
it.
-/


namespace MathlibExt.Combinatorics.Order.FinitePosets

-- Finite antichain covers.

/-- `C` is a finite family of antichains whose union is all of `α`. -/
def IsAntichainCoverFin {α : Type*} [PartialOrder α] (C : Finset (Finset α)) : Prop :=
  (∀ s ∈ C, IsAntichain (· ≤ ·) (s : Set α)) ∧ ∀ a : α, ∃ s ∈ C, a ∈ s

-- Natural-number invariants via sup/inf over powersets (avoids heavy `Fintype (Finset α)`).

open Classical in
/-- The largest cardinality of a chain in `α`. -/
noncomputable def maxChainSize
    (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  ((Finset.univ : Finset α).powerset).sup fun s =>
    if IsChain (· ≤ ·) (s : Set α) then s.card else 0

open Classical in
/-- The smallest number of antichains covering `α`. -/
noncomputable def minAntichainCoverSize
    (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  let all : Finset (Finset (Finset α)) := (Finset.univ.powerset).powerset
  let valid := all.filter fun C => IsAntichainCoverFin (α := α) C
  if h : valid.Nonempty then valid.inf' h fun C => C.card else 0

-- Helpers for Mirsky's theorem: rank each element by the longest chain ending at it.

open Classical in
noncomputable def chainHeightOf {α : Type*} [Fintype α]
    [PartialOrder α] (a : α) : ℕ :=
  ((Finset.univ : Finset α).powerset).sup fun s =>
    if IsChain (· ≤ ·) (s : Set α) ∧ a ∈ (s : Set α) ∧ ∀ b ∈ (s : Set α), b ≤ a
    then s.card else 0

noncomputable def mirskyCover {α : Type*} [Fintype α] [DecidableEq α]
    [PartialOrder α] : Finset (Finset α) :=
  (Finset.Icc 1 (maxChainSize α)).image fun i =>
    Finset.univ.filter fun a => chainHeightOf (α := α) a = i

end MathlibExt.Combinatorics.Order.FinitePosets
