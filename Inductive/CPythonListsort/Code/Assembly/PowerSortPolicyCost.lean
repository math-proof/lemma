/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean -/

import Def.CPythonListsort.Code.Assembly.MergePolicyReplay.Part4
import Def.CPythonListsort.Code.Assembly.PowerTreeEntropy
import Def.CPythonListsort.Code.Policy.BoundaryPowerGeometry
import Def.CPythonListsort.Code.Assembly.PowerSortPolicyCost
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

/-- A forest tiles the suffix from `start` to the end of `input` with positive,
in-bounds spans.  The recursive endpoint is also the next root's base, so this
single relation exposes start, adjacency, containment, and exact suffix
coverage without hiding any of them behind list arithmetic. -/
inductive OpenSpanChain (input : RunSpan) :
    Nat → List SpannedMergeTree → Prop
  | empty {start : Nat} (end_eq : start = input.endIndex) :
      OpenSpanChain input start []
  | cons {start : Nat} (entry : SpannedMergeTree)
      (rest : List SpannedMergeTree)
      (base_eq : entry.span.base = start)
      (valid : entry.span.ValidWithin input)
      (tail : OpenSpanChain input entry.span.endIndex rest) :
      OpenSpanChain input start (entry :: rest)

/-- Exact boundary powers together with the local heap edge from every open
root except the newest one.  The terminal open root is explicitly a leaf,
matching the scan loop's merge-before-push order. -/
inductive OpenBoundaryCertificate (input : RunSpan) :
    List SpannedMergeTree → List Nat → Prop
  | empty : OpenBoundaryCertificate input [] []
  | singleton (entry : SpannedMergeTree) (length : Nat)
      (isLeaf : entry.tree = .leaf length) :
      OpenBoundaryCertificate input [entry] []
  | cons (left right : SpannedMergeTree)
      (rest : List SpannedMergeTree) (power : Nat) (powers : List Nat)
      (power_eq : power = replayBoundaryPower input left.span right.span)
      (below_left_root : ∀ rootPower,
        left.tree.rootPower = some rootPower → power < rootPower)
      (tail : OpenBoundaryCertificate input (right :: rest) powers) :
      OpenBoundaryCertificate input (left :: right :: rest) (power :: powers)

end RunSpan
end CPythonListsort
