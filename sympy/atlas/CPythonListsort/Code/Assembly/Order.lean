/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/Order.lean -/

import sympy.atlas.CPythonListsort.Code.Transcription.Comparator
import Mathlib.Data.List.Sort

/-!
# Order, sortedness, and occurrence-level stability specifications

The sorting implementation accepts a total Boolean comparator.  Correctness
adds a strict-weak-order hypothesis only at the theorem boundary.  Stability
is phrased over occurrence tags that are attached to the input before any
movement; the output cannot be retagged after sorting.
-/

namespace CPythonListsort

universe u

/-- Mathlib's strict-weak-order laws for the Prop-valued relation exposed by a
Boolean comparator.  This structure deliberately contains no sorting result. -/
structure BoolStrictWeakOrder {α : Type u} (lt : BoolComparator α) : Prop extends
    IsStrictWeakOrder α (fun a b => lt a b = true)

/-- Comparator equivalence: neither value is strictly before the other. -/
def ComparatorEquivalent (lt : BoolComparator α) (a b : α) : Prop :=
  lt a b = false ∧ lt b a = false

/-- An array is sorted when no later entry strictly precedes an earlier one. -/
def Sorted (lt : BoolComparator α) (ys : Array α) : Prop :=
  ys.toList.Pairwise (fun earlier later => lt later earlier = false)

/-- A value together with the position of that exact input occurrence. -/
structure Occurrence (α : Type u) where
  value : α
  origin : Nat
  deriving DecidableEq, Repr

/-- Attach immutable origin tags before sorting begins. -/
def tagOccurrences (xs : Array α) : Array (Occurrence α) :=
  xs.zipIdx.map fun entry =>
    { value := entry.1, origin := entry.2 }

/-- Compare tagged occurrences only through their externally visible values. -/
def occurrenceComparator (lt : BoolComparator α) : BoolComparator (Occurrence α) :=
  fun a b => lt a.value b.value

/-- Strict-weak-order laws lift through occurrence tagging because the
comparator deliberately ignores the immutable origin field.  Merge and scan
correctness use this public bridge when applying order theorems to the actual
tagged keys moved by the transcription. -/
theorem BoolStrictWeakOrder.occurrenceComparator
    {lt : BoolComparator α} (h : BoolStrictWeakOrder lt) :
    BoolStrictWeakOrder (occurrenceComparator lt) := by
  exact
    { toIsStrictWeakOrder :=
        { toIsStrictOrder :=
            { toIrrefl := ⟨fun occurrence => h.irrefl occurrence.value⟩
              toIsTrans :=
                ⟨fun first second third hfirstSecond hsecondThird =>
                  h.trans first.value second.value third.value hfirstSecond
                    hsecondThird⟩ }
          incomp_trans := fun first second third hfirstSecond hsecondThird =>
            h.incomp_trans first.value second.value third.value hfirstSecond
              hsecondThird } }

/-- An occurrence sequence is a stable permutation of an explicitly chosen
canonical occurrence sequence.  This is the shared stability predicate for
both whole-sort results and intermediate consumed segments: callers choose the
canonical sequence, but may not retag the output after the fact. -/
def StableOccurrencePermutation (lt : BoolComparator α)
    (canonical output : List (Occurrence α)) : Prop :=
  output.Perm canonical ∧
    output.Pairwise fun earlier later =>
      ComparatorEquivalent lt earlier.value later.value →
        earlier.origin < later.origin

/-- A modeled output whose occurrence tags have travelled with its values. -/
structure TaggedOutput (α : Type u) where
  occurrences : Array (Occurrence α)
  deriving DecidableEq, Repr

/-- Erase carried origin tags to obtain the externally observable values. -/
def TaggedOutput.values (ys : TaggedOutput α) : Array α :=
  ys.occurrences.map Occurrence.value

/-- The tagged input from which a sorting execution starts.  Sorting code must
move these records, rather than manufacture origins after producing values. -/
def TaggedOutput.fromInput (xs : Array α) : TaggedOutput α :=
  ⟨tagOccurrences xs⟩

/-- Occurrence-level stability.  The permutation clause ties every final tag
to the canonical tag attached to the input, while the pairwise clause keeps
comparator-equivalent occurrences in increasing original-index order. -/
def Stable (lt : BoolComparator α) (xs : Array α) (ys : TaggedOutput α) : Prop :=
  StableOccurrencePermutation lt (tagOccurrences xs).toList
    ys.occurrences.toList
