/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/CountRunCorrectness.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.CountRunSafety
import sympy.atlas.CPythonListsort.Code.Assembly.Order
import sympy.atlas.CPythonListsort.Code.Correctness.ReverseSliceCorrectness
import sympy.atlas.CPythonListsort.Code.Correctness.SortSliceRange
import sympy.atlas.CPythonListsort.Code.Correctness.DescendingRunNormalization
import sympy.atlas.CPythonListsort.Code.Correctness.DescendingRunInvariant
import Lemma.List.Atlas.CPythonListsort.Code.Correctness.ReverseRangeSupport
import sympy.atlas.CPythonListsort.Code.Correctness.ScanRemainder

/-!
# Functional correctness of `count_run`

This file proves that the actual bounded `countRun?` transcription returns a
nonempty sorted run, preserves whole key/payload entries, and preserves the
origin order of comparator-equivalent occurrences.  The public theorem is
tied to `countRunTraced?` through the reviewed `countRun_safe` exact-erasure
certificate; no second run detector is substituted for the transcribed one.

The descending case follows CPython's two-level reversal literally.  Equal
blocks are reversed as the scan discovers them, the final equal block is
reversed at the boundary, and then the complete descending prefix is
reversed.  Thus the temporary order inside equal blocks is not exposed by the
public postcondition.
-/

namespace CPythonListsort

universe u v w x

variable {alpha : Type u} {nu : Type v}
variable {beta : Type w} {rho : Type x}

/-- The input-side condition needed for occurrence stability: within the
remaining source range, comparator-equivalent occurrences already appear in
increasing origin order.  The permutation half is deliberately the reflexive
one, so this is the shared `StableOccurrencePermutation` predicate rather
than a weaker local surrogate. -/
def CountRunCanonicalRange (lt : BoolComparator alpha)
    (slice : SortSlice (Occurrence alpha) nu) (base count : Nat) : Prop :=
  let canonical := (sortSliceRangeKeys slice base count).toList
  StableOccurrencePermutation lt canonical canonical

/-- Public semantic packet for one successful invocation of `count_run`.

`entryPermutation` mentions whole key/payload entries.  `stable` separately
mentions the occurrence-carrying key projection.  `frame` uses the shared
range-frame vocabulary consumed by run-formation correctness. -/
structure CountRunCorrectnessPost
    (lt : BoolComparator alpha)
    (state : MergeState (Occurrence alpha) nu)
    (before : SortSlice (Occurrence alpha) nu)
    (base : Int) (nremaining : Nat)
    (result : CountRunResult (Occurrence alpha) nu) : Prop where
  safety : CountRunSafetyPost state before base nremaining result
  lengthBounds : 1 <= result.length ∧ result.length <= nremaining
  minimumLength : nremaining = 1 ∨ 2 ≤ result.length
  sorted :
    Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys result.slice base.toNat result.length)
  stable :
    StableOccurrencePermutation lt
      (sortSliceRangeKeys before base.toNat result.length).toList
      (sortSliceRangeKeys result.slice base.toNat result.length).toList
  entryPermutation :
    (sortSliceRangeEntries result.slice base.toNat result.length).toList.Perm
      (sortSliceRangeEntries before base.toNat result.length).toList
  frame :
    SortSlice.EqualOutsideRange before result.slice base.toNat result.length

/-- The functional part of `CountRunCorrectnessPost`, separated internally so
it can be established from the raw evaluator before the traced safety witness
is identified through exact erasure. -/
private structure CountRunSemanticPost
    (lt : BoolComparator alpha)
    (before : SortSlice (Occurrence alpha) nu)
    (start nremaining : Nat)
    (result : CountRunResult (Occurrence alpha) nu) : Prop where
  fuel : result.fuelExhausted = false
  lengthBounds : 1 ≤ result.length ∧ result.length ≤ nremaining
  minimumLength : nremaining = 1 ∨ 2 ≤ result.length
  sorted :
    Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys result.slice start result.length)
  stable :
    StableOccurrencePermutation lt
      (sortSliceRangeKeys before start result.length).toList
      (sortSliceRangeKeys result.slice start result.length).toList
  entryPermutation :
    (sortSliceRangeEntries result.slice start result.length).toList.Perm
      (sortSliceRangeEntries before start result.length).toList
  frame :
    SortSlice.EqualOutsideRange before result.slice start result.length

private structure AscendingCorrectnessPost
    (lt : BoolComparator alpha)
    (slice : SortSlice (Occurrence alpha) nu)
    (start n nremaining : Nat)
    (result : AscendingScanResult) : Prop where
  fuel : result.fuelExhausted = false
  lengthBounds : n ≤ result.length ∧ result.length ≤ nremaining
  sorted :
    Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys slice start result.length)
  stoppedByDecrease :
    result.length < nremaining ->
      ∃ previous next,
        slice.read? (Int.ofNat start + Int.ofNat (result.length - 1)) =
            some previous ∧
          slice.read? (Int.ofNat start + Int.ofNat result.length) =
            some next ∧
          occurrenceComparator lt next.key previous.key = true

private structure ReverseLastEqualCorrectnessPost
    (before : SortSlice beta rho) (start n neq : Nat)
    (result : ReverseEqualResult beta rho) : Prop where
  resultEq :
    reverseLastEqual? before (Int.ofNat start) n neq = some result
  fuel : result.fuelExhausted = false
  entries :
    (sortSliceRangeEntries result.slice start n).toList =
      DescendingRunSpec.reverseSuffix
        (sortSliceRangeEntries before start n).toList (neq + 1)
  keys :
    (sortSliceRangeKeys result.slice start n).toList =
      DescendingRunSpec.reverseSuffix
        (sortSliceRangeKeys before start n).toList (neq + 1)
  frame : SortSlice.EqualOutsideRange before result.slice start n

private structure DescendingMachineInvariant
    (lt : BoolComparator alpha)
    (source current : SortSlice (Occurrence alpha) nu)
    (start n neq : Nat) : Prop where
  frame : SortSlice.EqualOutsideRange source current start n
  keys :
    DescendingRunSpec.Invariant lt
      (sortSliceRangeKeys source start n).toList
      (sortSliceRangeKeys current start n).toList (neq + 1)
  entries :
    (DescendingRunSpec.normalize
      (sortSliceRangeEntries current start n).toList (neq + 1)).Perm
        (sortSliceRangeEntries source start n).toList

private structure DescendingScanCorrectnessPost
    (lt : BoolComparator alpha)
    (source : SortSlice (Occurrence alpha) nu)
    (start n nremaining neq : Nat)
    (result : DescendingScanResult (Occurrence alpha) nu) : Prop where
  fuel : result.fuelExhausted = false
  lengthBounds : n ≤ result.length ∧ result.length ≤ nremaining
  invariant :
    DescendingMachineInvariant lt source result.slice start result.length
      result.equalTail

private structure ExactReverseRangePost
    (before : SortSlice beta rho) (start count : Nat)
    (result : ReverseSliceResult beta rho) : Prop where
  resultEq :
    sortsliceReverse? before (Int.ofNat start) count = some result
  fuel : result.fuelExhausted = false
  entries :
    (sortSliceRangeEntries result.slice start count).toList =
      (sortSliceRangeEntries before start count).toList.reverse
  keys :
    (sortSliceRangeKeys result.slice start count).toList =
      (sortSliceRangeKeys before start count).toList.reverse
  frame : SortSlice.EqualOutsideRange before result.slice start count

/-! ## Concrete semantic regressions -/

private def countRunCorrectnessOccurrence (value origin : Nat) :
    Occurrence Nat :=
  { value := value, origin := origin }

private def countRunCorrectnessEntry (value origin payload : Nat) :
    SortSliceEntry (Occurrence Nat) Nat :=
  { key := countRunCorrectnessOccurrence value origin
    value := some payload }

private def countRunCorrectnessState
    (slice : SortSlice (Occurrence Nat) Nat) :
    MergeState (Occurrence Nat) Nat :=
  { min_gallop := MIN_GALLOP
    listlen := slice.entries.size
    basekeys := 0
    data := slice
    a := { cells := #[], backing := .inline, hasValues := true }
    alloced := 0
    pending := #[]
    key_compare := occurrenceComparator fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def countRunCorrectnessTaggedEqualSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[countRunCorrectnessEntry 3 0 30,
        countRunCorrectnessEntry 2 1 20,
        countRunCorrectnessEntry 2 2 21,
        countRunCorrectnessEntry 1 3 10] }

private def countRunCorrectnessAllEqualSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[countRunCorrectnessEntry 2 0 20,
        countRunCorrectnessEntry 2 1 21,
        countRunCorrectnessEntry 2 2 22] }

private def countRunCorrectnessExtensionSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[countRunCorrectnessEntry 3 0 30,
        countRunCorrectnessEntry 2 1 20,
        countRunCorrectnessEntry 1 2 10,
        countRunCorrectnessEntry 3 3 31,
        countRunCorrectnessEntry 4 4 40,
        countRunCorrectnessEntry 5 5 50,
        countRunCorrectnessEntry 0 6 0] }

private def countRunCorrectnessNonzeroBaseSlice :
    SortSlice (Occurrence Nat) Nat :=
  { entries :=
      #[countRunCorrectnessEntry 99 0 990,
        countRunCorrectnessEntry 3 1 30,
        countRunCorrectnessEntry 2 2 20,
        countRunCorrectnessEntry 1 3 10,
        countRunCorrectnessEntry 77 4 770] }
