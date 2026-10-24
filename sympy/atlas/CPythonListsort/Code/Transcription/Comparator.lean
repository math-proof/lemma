/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/Comparator.lean -/

import Mathlib

/-!
# Total Boolean comparator model

Version one replaces CPython's fallible and potentially specialized comparison
dispatch with a pure total Boolean function.  Keeping `iflt` as the single
entry point preserves the argument and call order of every transcribed `IFLT`
site while making the deliberate modeling boundary visible in Lean.
-/

namespace CPythonListsort

universe u

/-- The version-one model of CPython's comparison callback. -/
abbrev BoolComparator (α : Type u) := α → α → Bool

/-- The transcription boundary corresponding to CPython's `IFLT(x, y)` macro. -/
@[inline]
def iflt (lt : BoolComparator α) (x y : α) : Bool :=
  lt x y
