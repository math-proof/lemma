/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/BinarysortCorrectness.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.BinarysortSafety
import sympy.atlas.CPythonListsort.Code.Assembly.Order
import sympy.atlas.CPythonListsort.Code.Correctness.SortSliceRange
import Mathlib.Data.List.InsertIdx

/-!
# Functional correctness of `binarysort`

This file proves correctness of the reviewed binary-insertion transcription on
occurrence-carrying keys.  The proof is about the same traced execution covered
by `binarysort_safe`: raw functional correctness is identified with that result
through exact erasure, rather than through a second sorting implementation.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}
variable {beta kappa rho : Type*}

/-- Mathematical effect of saving the entry at `stop`, shifting
`[insert, stop)` one cell right, and writing the saved entry at `insert`. -/
private def insertEarlierEntries (xs : Array beta) (insert stop : Nat)
    (pivot : beta) : Array beta :=
  ((xs.extract 0 insert ++ #[pivot]) ++ xs.extract insert stop) ++
    xs.extract (stop + 1) xs.size

/-! ## Upper-bound search semantics -/

private structure BinarySearchSemanticPost
    (cmp : BoolComparator kappa) (slice : SortSlice kappa rho)
    (base : Nat) (pivot : SortSliceEntry kappa rho) (ok : Nat)
    (result : BinarySearchResult) : Prop where
  rangeStop : base + ok ≤ slice.entries.size
  fuel : result.fuelExhausted = false
  positionLe : result.position ≤ ok
  beforeFalse : ∀ i (hi : i < result.position),
    cmp pivot.key (slice.entries[base + i]'(by
      exact lt_of_lt_of_le
        (Nat.add_lt_add_left (lt_of_lt_of_le hi positionLe) base)
        rangeStop)).key = false
  afterTrue : ∀ i (_ : result.position ≤ i) (hi : i < ok),
    cmp pivot.key (slice.entries[base + i]'(by
      exact lt_of_lt_of_le (Nat.add_lt_add_left hi base) rangeStop)).key = true

/-! ## One stable insertion step -/

/-- Move the entry selected at `k` to insertion point `p`. -/
private def moveEarlier (xs : List beta) (p k : Nat) (pivot : beta) : List beta :=
  xs.take p ++ pivot :: ((xs.drop p).take (k - p) ++ xs.drop (k + 1))

/-! ## Raw outer-loop correctness -/

private structure BinarysortLoopCorrectnessPost
    (lt : BoolComparator alpha) (canonical : List (Occurrence alpha))
    (state : MergeState (Occurrence alpha) nu)
    (before : SortSlice (Occurrence alpha) nu)
    (base n ok fuel : Nat) (result : BinarysortResult (Occurrence alpha) nu) : Prop where
  resultEq : binarysortLoop? fuel state before (Int.ofNat base) n ok = some result
  resultFuel : result.fuelExhausted = false
  sorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys result.slice base n)
  stable : StableOccurrencePermutation lt canonical
    (sortSliceRangeKeys result.slice base n).toList
  rangeEntriesPerm :
    (sortSliceRangeEntries result.slice base n).toList.Perm
      (sortSliceRangeEntries before base n).toList
  frame : SortSlice.EqualOutsideRange before result.slice base n

/-- Public correctness certificate for the exact traced `binarysort`
execution.  The stability premise is intentionally attached to the whole
target range: binary insertion preserves the pre-existing order of equal
occurrences, so it cannot repair an already non-canonical equal-key suffix. -/
structure BinarysortCorrectnessPost
    (lt : BoolComparator alpha) (canonical : List (Occurrence alpha))
    (state : MergeState (Occurrence alpha) nu)
    (before : SortSlice (Occurrence alpha) nu)
    (base n ok : Nat) (result : BinarysortResult (Occurrence alpha) nu) : Prop where
  safety : BinarysortSafetyPost state before (Int.ofNat base) n ok result
  sorted : Sorted (occurrenceComparator lt)
    (sortSliceRangeKeys result.slice base n)
  stable : StableOccurrencePermutation lt canonical
    (sortSliceRangeKeys result.slice base n).toList
  rangeEntriesPerm :
    (sortSliceRangeEntries result.slice base n).toList.Perm
      (sortSliceRangeEntries before base n).toList
  frame : SortSlice.EqualOutsideRange before result.slice base n
  beforeFrame : ∀ k, k < base → result.slice.entries[k]? = before.entries[k]?
  afterFrame : ∀ k, base + n ≤ k →
    result.slice.entries[k]? = before.entries[k]?

private def binarysortCorrectnessNatLt : BoolComparator Nat :=
  fun left right => decide (left < right)

private def binarysortCorrectnessEqualSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[{ key := { value := 1, origin := 0 }, value := some 10 },
        { key := { value := 1, origin := 1 }, value := some 11 },
        { key := { value := 2, origin := 2 }, value := some 20 },
        { key := { value := 1, origin := 3 }, value := some 12 }] }

private def binarysortCorrectnessEqualState :
    MergeState (Occurrence Nat) Nat :=
  { min_gallop := MIN_GALLOP
    listlen := 4
    basekeys := 0
    data := binarysortCorrectnessEqualSlice
    a := { cells := #[], backing := .inline, hasValues := true }
    alloced := 0
    pending := #[]
    key_compare := occurrenceComparator binarysortCorrectnessNatLt
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def binarysortCorrectnessOffsetSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[{ key := { value := 99, origin := 90 }, value := some 900 },
        { key := { value := 2, origin := 0 }, value := some 20 },
        { key := { value := 1, origin := 1 }, value := some 10 },
        { key := { value := 2, origin := 2 }, value := some 21 },
        { key := { value := 88, origin := 91 }, value := some 800 }] }

private def binarysortCorrectnessOffsetState :
    MergeState (Occurrence Nat) Nat :=
  { binarysortCorrectnessEqualState with
    listlen := 5
    data := binarysortCorrectnessOffsetSlice }
