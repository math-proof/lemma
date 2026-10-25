/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Correctness/DescendingRunNormalization.lean -/

import Mathlib
/-!
# Pure normalization algebra for descending natural runs

During `count_run`, the most recent comparator-equivalence block is reversed
before scanning continues.  At the end the whole descending prefix is
reversed.  These list identities isolate that double-reversal bookkeeping from
the executable array proof.
-/


namespace CPythonListsort

namespace DescendingRunSpec

/-- Reverse the final `tailLength` entries of a scanned descending prefix. -/
def reverseSuffix (xs : List α) (tailLength : Nat) : List α :=
  xs.take (xs.length - tailLength) ++
    (xs.drop (xs.length - tailLength)).reverse

/-- Stable ascending result represented by a descending prefix whose final
equivalence block has length `tailLength`. -/
def normalize (xs : List α) (tailLength : Nat) : List α :=
  xs.drop (xs.length - tailLength) ++
    (xs.take (xs.length - tailLength)).reverse

end DescendingRunSpec
end CPythonListsort
