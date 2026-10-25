/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean -/

import Def.CPythonListsort.Code.Assembly.MergePolicyReplay.Part4
import Def.CPythonListsort.Code.Assembly.PowerTreeEntropy
import Def.CPythonListsort.Code.Policy.BoundaryPowerGeometry
/-!
# PowerSort policy and cost bridge

This module contains the geometry used to turn the implementation's open
merge forest into the min-Cartesian PowerSort tree.  In particular, absorbing
the subtree on the deeper side of three consecutive spans leaves the
shallower boundary power unchanged.  The statements use the same `RunSpan`
and `replayBoundaryPower` objects as the executable policy replay, so no
paper-level midpoint oracle is introduced at the bridge.
-/


namespace CPythonListsort

namespace RunSpan

/-- A positive source span lying inside a declared input span. -/
def ValidWithin (span input : RunSpan) : Prop :=
  input.base ≤ span.base ∧
    span.endIndex ≤ input.endIndex ∧
    0 < span.len

/-! ## Certified open forests and canonical final completion -/

/-- The span lengths of the roots currently open on the pending stack. -/
def openForestLengths (forest : List SpannedMergeTree) : List Nat :=
  forest.map fun entry => entry.span.len

end RunSpan
end CPythonListsort
