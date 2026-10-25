/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean -/

import Def.CPythonListsort.Code.Assembly.MergePolicyReplay.Part4
import Def.CPythonListsort.Code.Assembly.PowerTreeEntropy
import Def.CPythonListsort.Code.Policy.BoundaryPowerGeometry
import Def.CPythonListsort.Code.Assembly.PowerSortPolicyCost.Part2
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

/-! ## From the open certificate to a valid PowerSort plan -/

/-- Completion of a certified suffix retains its exact source interval and
the expected global `PowerValid` judgment.  The final field identifies the
root label with the first open-boundary power, or with `none` for the terminal
leaf. -/
structure CanonicalTopPairRootPost (input : RunSpan) (start : Nat)
    (powers : List Nat) (root : SpannedMergeTree) : Prop where
  base_eq : root.span.base = start
  end_eq : root.span.endIndex = input.endIndex
  spanValid : root.span.ValidWithin input
  spannedValid : root.Valid
  powerValid : root.tree.PowerValid input.base
    (BitVec.ofNat 64 input.len) start
  rootPower_eq : root.tree.rootPower = powers.head?

end RunSpan
end CPythonListsort
