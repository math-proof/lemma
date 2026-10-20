/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Index.lean -/

import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.PNat.Basic

/-!
# Multiple-zeta indices

This file defines multiple-zeta indices, admissibility for bundled and list
representations, and Hoffman blocks in a two-letter free monoid.

## Main definitions

* `MetaMathlibExt.MultipleZeta.Index`
* `MetaMathlibExt.MultipleZeta.Index.entries`
* `MetaMathlibExt.MultipleZeta.Index.weight`
* `MetaMathlibExt.MultipleZeta.Index.depth`
* `MetaMathlibExt.MultipleZeta.Index.height`
* `MetaMathlibExt.MultipleZeta.Index.IsAdmissible`
* `MetaMathlibExt.MultipleZeta.IsAdmissible`
* `MetaMathlibExt.MultipleZeta.hoffmanBlock`

## Main theorems

* `MetaMathlibExt.MultipleZeta.Index.isAdmissible_iff`
* `MetaMathlibExt.MultipleZeta.toList_hoffmanBlock`
-/

namespace MetaMathlibExt.MultipleZeta

/-- An index is an ordered finite sequence of positive natural numbers,
permitting the empty sequence, packaged as compositions over all total
weights. Source clause D1 (`2608.10675:D01`, `2307.09867:D01`). -/
def Index : Type :=
  Σ _n : Nat, Composition _n

/-- Entries of an index in source order. Source clause D2
(`2608.10675:D01`, `2307.09867:D01`). -/
def Index.entries : Index → List Nat
  | ⟨_, c⟩ => c.blocks

/-- Weight of an index: the sum of its entries. Source clause D3
(`2307.09867:D01`). -/
def Index.weight : Index → Nat
  | ⟨n, _⟩ => n

/-- Depth of an index: the number of entries. Source clause D4
(`2608.10675:D01`, `2307.09867:D01`). -/
def Index.depth : Index → Nat
  | ⟨_, c⟩ => Composition.length c

/-- Height of an index: the number of entries at least two. Source clause D5
(`2307.09867:D01`). -/
def Index.height : Index → Nat
  | ⟨_, c⟩ => (c.blocks.filter (· ≥ 2)).length

/-- Admissibility: the index is nonempty and its first entry is at least two.
Source clause D6 (`2307.09867:D01`). -/
def Index.IsAdmissible : Index → Prop
  | ⟨_, c⟩ =>
    match c.blocks with
    | [] => False
    | h :: _ => 2 ≤ h

/-- Admissibility predicate for multiple-zeta indices in decreasing summation
order. A list is admissible when it is nonempty, every entry is positive, and
the first entry is at least two. Source `2307.09867:D01`. -/
def IsAdmissible : List ℕ → Prop
  | [] => False
  | h :: t => 2 ≤ h ∧ ∀ x ∈ t, 0 < x

@[simp]
theorem isAdmissible_nil : ¬IsAdmissible [] := by
  simp [IsAdmissible]

@[simp]
theorem isAdmissible_cons_iff (h : ℕ) (t : List ℕ) :
    IsAdmissible (h :: t) ↔ 2 ≤ h ∧ ∀ x ∈ t, 0 < x := by
  rfl

/-- The bundled and list formulations of admissibility agree. -/
theorem Index.isAdmissible_iff (index : Index) :
    index.IsAdmissible ↔ MetaMathlibExt.MultipleZeta.IsAdmissible index.entries := by
  rcases index with ⟨_, c⟩
  cases hblocks : c.blocks with
  | nil => simp [Index.IsAdmissible, Index.entries, IsAdmissible, hblocks]
  | cons h t =>
      simp only [Index.IsAdmissible, Index.entries, IsAdmissible, hblocks]
      constructor
      · intro hh
        refine ⟨hh, fun x hx => c.blocks_pos ?_⟩
        simpa [hblocks] using List.mem_cons_of_mem h hx
      · exact fun h => h.1

/-- Hoffman block word `z_k = x ^ (k - 1) * y` for positive `k` in
`FreeMonoid Bool`, with `false` representing `x` and `true` representing `y`.
Source `2307.09867:D05`. -/
def hoffmanBlock (k : PNat) : FreeMonoid Bool :=
  FreeMonoid.ofList (List.replicate (k.val - 1) false ++ [true])

/-- Reading a Hoffman block as a list recovers `k - 1` copies of `x` followed
by one `y`. -/
@[simp]
theorem toList_hoffmanBlock (k : PNat) :
    FreeMonoid.toList (hoffmanBlock k) =
      List.replicate (k.val - 1) false ++ [true] := by
  simp [hoffmanBlock]

end MetaMathlibExt.MultipleZeta
