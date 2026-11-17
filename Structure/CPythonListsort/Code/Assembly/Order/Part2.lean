/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/Order.lean -/

module

public import Def.CPythonListsort.Code.Transcription.Comparator
public import Mathlib.Data.List.Sort
public import Def.CPythonListsort.Code.Assembly.Order
/-!
# Order, sortedness, and occurrence-level stability specifications

The sorting implementation accepts a total Boolean comparator.  Correctness
adds a strict-weak-order hypothesis only at the theorem boundary.  Stability
is phrased over occurrence tags that are attached to the input before any
movement; the output cannot be retagged after sorting.
-/
public section




namespace CPythonListsort

universe u

/-- A value together with the position of that exact input occurrence. -/
structure Occurrence (α : Type u) where
  value : α
  origin : Nat
  deriving DecidableEq, Repr

end CPythonListsort
