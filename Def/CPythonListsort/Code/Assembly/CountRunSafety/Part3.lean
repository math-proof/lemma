/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/CountRunSafety.lean -/

import Def.CPythonListsort.Code.Assembly.ReverseSliceSafety.Part2
import Def.CPythonListsort.Code.Transcription.CountRun.Part4
import Theorem.CPythonListsort.Code.Assembly.CountRunSafety.Part7
/-!
# `count_run` safety

The evaluator below mirrors the reviewed `count_run` transcription while
producing its trace compositionally.  The Lean instrumentation reads the
previous entry and then the next entry; its comparator orientation and control
branch match CPython's `IF_NEXT_SMALLER`, without making a claim about C operand
evaluation order.  Every operational-equivalence-block, prefix, and whole-run
reversal delegates to the traced `sortslice_reverse` evaluator proved safe in
`ReverseSliceSafety`.

As in the v1 transcription, `BoolComparator` is total.  CPython's comparator
error/failure return path is therefore outside this model; the safety theorem is
for every total Boolean comparator, including inconsistent ones.
-/


namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-! ## Branch and failure anti-vacuity regressions -/

def countRunRegressionState (slice : SortSlice Nat Nat) :
    MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := slice.entries.size
    basekeys := 0
    data := slice
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending := #[]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

def countRunSingletonSlice : SortSlice Nat Nat :=
  { entries := #[{ key := 7, value := none }] }

def countRunAscendingSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 1, value := none }, { key := 2, value := none },
        { key := 3, value := none }, { key := 4, value := none }] }

def countRunDescendingSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 4, value := none }, { key := 3, value := none },
        { key := 2, value := none }, { key := 1, value := none }] }

def countRunGateSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 1, value := none }, { key := 3, value := none },
        { key := 2, value := none }] }

def countRunTaggedEqualSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 3, value := some 30 }, { key := 2, value := some 20 },
        { key := 2, value := some 21 }, { key := 1, value := some 10 }] }

def countRunValuesRegressionState (slice : SortSlice Nat Nat) :
    MergeState Nat Nat :=
  { countRunRegressionState slice with
    a := { cells := #[], backing := .inline, hasValues := true } }

def countRunExtensionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 3, value := none }, { key := 2, value := none },
        { key := 1, value := none }, { key := 3, value := none },
        { key := 4, value := none }, { key := 5, value := none },
        { key := 0, value := none }] }

def countRunConstantTrueState (slice : SortSlice Nat Nat) :
    MergeState Nat Nat :=
  { countRunRegressionState slice with key_compare := fun _ _ => true }

end CPythonListsort
