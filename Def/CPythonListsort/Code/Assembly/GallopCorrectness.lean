/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/GallopCorrectness.lean -/

import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopLeftSafety
import Lemma.List.Atlas.CPythonListsort.Code.Assembly.GallopRightSafety
import Def.CPythonListsort.Code.Assembly.Order.Part4
/-!
# Correctness of the two biased gallops

This module proves the partition contracts of the actual `gallopLeft?` and
`gallopRight?` transcriptions.  The search proof is factored through the direct
key-source evaluator used by the safety development; the public theorems erase
that evaluator back to the reviewed `SortSlice` functions.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- The key at logical source index `i` compares strictly before `key`. -/
def GallopBefore (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (i : Nat) : Prop :=
  ∃ entry, source.read? (Int.ofNat i) = some entry ∧ lt entry.key key = true

/-- The key compares strictly before the key at logical source index `i`. -/
def GallopAfter (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (i : Nat) : Prop :=
  ∃ entry, source.read? (Int.ofNat i) = some entry ∧ lt key entry.key = true

/-- A Boolean search predicate is a prefix on the searched range. -/
def GallopPrefix (predicate : Nat → Prop) (n : Nat) : Prop :=
  ∀ i j, i < j → j < n → predicate j → predicate i

/-- Exact boundary contract for a prefix predicate. -/
def GallopPartition (predicate : Nat → Prop) (n k : Nat) : Prop :=
  k ≤ n ∧
    (∀ i, i < k → predicate i) ∧
    (∀ i, k ≤ i → i < n → ¬predicate i)

/-- Pointwise sortedness of the physical run searched by a gallop.  This is
the index-facing form of the project's `Sorted` specification: no later key
strictly precedes an earlier key. -/
def GallopSortedRange (lt : BoolComparator κ)
    (source : GallopKeySource κ ν) (n : Nat) : Prop :=
  ∀ i j (_hi : i < n) (_hj : j < n), i < j →
    ∀ earlier later,
      source.read? (Int.ofNat i) = some earlier →
      source.read? (Int.ofNat j) = some later →
      lt later.key earlier.key = false

/-- A mathematical key array is exactly the `n` logical keys exposed by a
gallop source.  The size equality prevents a caller from padding or truncating
the array, and the pointwise clause identifies both the successful physical
read and its key. -/
def GallopKeyArrayAgreement (source : GallopKeySource κ ν) (n : Nat)
    (keys : Array κ) : Prop :=
  keys.size = n ∧
    ∀ i, i < n → ∃ entry,
      source.read? (Int.ofNat i) = some entry ∧
        keys[i]? = some entry.key

/-! ## Public exact partition contracts -/

/-- Exact left-biased partition on the reviewed materialized slice. -/
def GallopLeftPartition (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (key : κ) (n k : Nat) : Prop :=
  k ≤ n ∧
    (∀ i, i < k → ∃ entry,
      slice.read? (base + Int.ofNat i) = some entry ∧
        lt entry.key key = true) ∧
    (∀ i, k ≤ i → i < n → ∃ entry,
      slice.read? (base + Int.ofNat i) = some entry ∧
        lt entry.key key = false)

/-- Exact right-biased partition on the reviewed materialized slice. -/
def GallopRightPartition (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (key : κ) (n k : Nat) : Prop :=
  k ≤ n ∧
    (∀ i, i < k → ∃ entry,
      slice.read? (base + Int.ofNat i) = some entry ∧
        lt key entry.key = false) ∧
    (∀ i, k ≤ i → i < n → ∃ entry,
      slice.read? (base + Int.ofNat i) = some entry ∧
        lt key entry.key = true)

/-! ## Equality-bias regressions -/

def gallopDuplicateRegressionSlice : SortSlice Nat PUnit :=
  { entries := #[
      { key := 1, value := none },
      { key := 2, value := none },
      { key := 2, value := none },
      { key := 3, value := none }] }

def gallopDuplicateRegressionState : MergeState Nat PUnit :=
  { min_gallop := 7
    listlen := 4
    basekeys := 0
    data := gallopDuplicateRegressionSlice
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending := #[]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

end CPythonListsort
