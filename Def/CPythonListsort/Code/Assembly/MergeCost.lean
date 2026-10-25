/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeCost.lean -/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic
import Structure.CPythonListsort.Code.Assembly.MergeCost
/-!
# Merge-cost accounting

This module isolates the implementation-independent arithmetic behind the
Munro--Wild PowerSort merge-cost bound.  Run lengths and merge costs remain
natural numbers; entropy and the final inequality live in `ℝ`.

An empty `MergePlan` represents the empty input.  A nonempty plan is a binary
tree whose leaves are the runs, in input order.  Internal powers are retained
for the later PowerSort-policy bridge but do not affect merge-cost accounting.
-/


namespace CPythonListsort

namespace RunProfile

/-- Real-valued run fractions, with Lean's totalized division convention at
total length zero. -/
noncomputable def fractions (profile : RunProfile n) : List ℝ :=
  profile.lengths.map fun length : Nat => (length : ℝ) / (n : ℝ)

end RunProfile

/-- One base-two Shannon entropy summand, using `0⁻¹ = 0` and
`Real.logb 2 0 = 0` at the zero endpoint. -/
noncomputable def binaryEntropyTerm (p : ℝ) : ℝ :=
  p * Real.logb 2 p⁻¹

/-- Base-two Shannon entropy of a finite real-valued weight list. -/
noncomputable def binaryEntropy (weights : List ℝ) : ℝ :=
  (weights.map binaryEntropyTerm).sum

/-- Base-two entropy of the fractions represented by a run profile. -/
noncomputable def RunProfile.entropy (profile : RunProfile n) : ℝ :=
  binaryEntropy profile.fractions

end CPythonListsort
