/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.MergePolicyReplay
import sympy.atlas.CPythonListsort.Code.Assembly.PowerTreeEntropy
import sympy.atlas.CPythonListsort.Code.Policy.BoundaryPowerGeometry

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

/-- A reviewable certificate for a scan-produced open PowerSort forest.

`powers` is not inferred from a tree built after the fact: `boundaries`
aligns it with every adjacent pair of open roots and records the exact
transcribed boundary power.  `strict` is the pending-stack heap order, while
`below_left_root` inside `OpenBoundaryCertificate` records the remaining
heap edges into already-built subtrees. -/
structure PowerOpenForestCertificate (input : RunSpan) (start : Nat)
    (forest : List SpannedMergeTree) (powers : List Nat) : Prop where
  inputMax : input.len ≤ PY_LIST_MAX
  spans : OpenSpanChain input start forest
  treeValid : ∀ entry ∈ forest,
    entry.Valid ∧
      entry.tree.PowerValid input.base (BitVec.ofNat 64 input.len)
        entry.span.base
  boundaries : OpenBoundaryCertificate input forest powers
  strict : powers.Pairwise (fun earlier later => earlier < later)

/-- The top-level scan certificate starts at the input base. -/
def PowerOpenForestValid (input : RunSpan)
    (forest : List SpannedMergeTree) : Prop :=
  ∃ powers, PowerOpenForestCertificate input input.base forest powers

/-- Right-associated tree obtained by repeatedly merging the top pair of a
nonempty open forest.  Its node label is recomputed from the full aggregate
child spans, rather than copied from certificate metadata. -/
def canonicalTopPairRoot (input : RunSpan) :
    SpannedMergeTree → List SpannedMergeTree → SpannedMergeTree
  | current, [] => current
  | current, next :: rest =>
      let right := canonicalTopPairRoot input next rest
      SpannedMergeTree.merge
        (replayBoundaryPower input current.span right.span) current right

/-- Empty-or-tree normalization of canonical repeated-top-pair completion. -/
def canonicalTopPairCompletion (input : RunSpan) :
    List SpannedMergeTree → MergePlan
  | [] => .empty
  | first :: rest => .tree (canonicalTopPairRoot input first rest).tree

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
