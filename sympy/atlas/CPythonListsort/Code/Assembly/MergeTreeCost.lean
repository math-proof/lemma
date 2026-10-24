/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergeTreeCost.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.AccessTrace
import sympy.atlas.CPythonListsort.Code.Assembly.MergeCost

/-!
# Logical merge replay and final-collapse cost dominance

`MergeCost` defines the paper-facing merge tree, merge cost, weighted path
length, and their exact equality.  This module adds two pure pieces needed by
the implementation bridge:

* checked replay of the raw, pre-trim logical merge observations; and
* the exact length-and-cost semantics of CPython's `merge_force_collapse`,
  together with a proof that it costs no more than Algorithm 2's canonical
  top-pair completion.

The paper's Algorithm 2 always merges the top pair in its final loop.  CPython
has one additional branch: for a final triple `A, B, C`, it merges `A` with
`B` when `|A| < |C|`.  This is a cost-nonincreasing local tree rotation, not a
tree-equality fact.
-/

namespace CPythonListsort

/-! ## Checked replay of logical pre-trim merges -/

namespace RunSpan

/-- The first index after a run span. -/
def endIndex (span : RunSpan) : Nat :=
  span.base + span.len

/-- The right span begins exactly where the left span ends. -/
def Adjacent (left right : RunSpan) : Prop :=
  left.endIndex = right.base

instance (left right : RunSpan) : Decidable (Adjacent left right) :=
  inferInstanceAs (Decidable (left.endIndex = right.base))

/-- The span produced by a logical merge of two adjacent runs. -/
def merge (left right : RunSpan) : RunSpan :=
  { base := left.base, len := left.len + right.len }

end RunSpan

/-- A merge tree paired with the source interval occupied by its root. -/
structure SpannedMergeTree where
  span : RunSpan
  tree : MergeTree
  deriving DecidableEq, Repr

namespace SpannedMergeTree

/-- The tree's leaf weights account for exactly the paired source span. -/
def Valid (entry : SpannedMergeTree) : Prop :=
  entry.tree.totalLength = entry.span.len

/-- Initial forest entry for one implementation-formed run. -/
def leaf (span : RunSpan) : SpannedMergeTree :=
  { span := span, tree := .leaf span.len }

/-- Logical combination of two adjacent forest entries.  The supplied power
is a semantic label only and does not affect merge-cost accounting. -/
def merge (power : Nat) (left right : SpannedMergeTree) : SpannedMergeTree :=
  { span := left.span.merge right.span
    tree := .merge power left.tree right.tree }

/-- A logical merge observation paired with the node-power label used in the
paper-facing tree.  The implementation trace supplies the raw event; the
PowerSort bridge supplies and verifies the label. -/
structure PoweredMergeReplayStep where
  event : LogicalMergeEvent
  power : Nat
  deriving DecidableEq, Repr

/-- Apply one checked logical merge to an ordered forest.  Replay verifies the
selected index, both historical pre-trim spans, and their adjacency before
constructing an internal node. -/
def applyPoweredMergeReplayStep? (forest : List SpannedMergeTree)
    (step : PoweredMergeReplayStep) : Option (List SpannedMergeTree) := do
  let left ← forest[step.event.index]?
  let right ← forest[step.event.index + 1]?
  if left.span = step.event.left ∧ right.span = step.event.right ∧
      step.event.left.Adjacent step.event.right then
    pure (forest.take step.event.index ++
      [left.merge step.power right] ++ forest.drop (step.event.index + 2))
  else
    none

/-- Replay chronological logical merge observations. -/
def replayPoweredMergeSteps? :
    List SpannedMergeTree → List PoweredMergeReplayStep →
      Option (List SpannedMergeTree)
  | forest, [] => some forest
  | forest, step :: steps => do
      let forest ← applyPoweredMergeReplayStep? forest step
      replayPoweredMergeSteps? forest steps

/-- A powered chronological trace completely merges the supplied formed runs
into the displayed result. -/
def CompleteMergeReplay (initial : List RunSpan)
    (steps : List PoweredMergeReplayStep) (result : SpannedMergeTree) : Prop :=
  replayPoweredMergeSteps? (initial.map .leaf) steps = some [result]

/-! ## Paper top-pair completion -/

/-- Every run length in a pending forest is positive. -/
def PositiveRunLengths (lengths : List Nat) : Prop :=
  ∀ length ∈ lengths, 0 < length

/-- Cost of Algorithm 2's final loop, which repeatedly merges the top two
pending runs.  Equivalently, this is the cost of the right-associated tree on
the listed open-subtree lengths. -/
def topPairCompletionCost : List Nat → Nat
  | [] => 0
  | [_] => 0
  | first :: second :: rest =>
      first + (second :: rest).sum +
        topPairCompletionCost (second :: rest)

/-- The chronological internal-node costs paid by Algorithm 2's final loop.

The recursive definition of `topPairCompletionCost` is written from the
oldest root outward; execution merges the newest pair first, so the current
whole-forest cost is appended after the recursive suffix schedule. -/
def topPairCompletionMergeCosts : List Nat → List Nat
  | [] => []
  | [_] => []
  | first :: second :: rest =>
      topPairCompletionMergeCosts (second :: rest) ++
        [(first :: second :: rest).sum]

/-- The explicit canonical completion schedule sums to its scalar cost. -/
theorem topPairCompletionMergeCosts_sum : ∀ lengths : List Nat,
    (topPairCompletionMergeCosts lengths).sum =
      topPairCompletionCost lengths
  | [] => rfl
  | [_] => rfl
  | first :: second :: rest => by
      rw [topPairCompletionMergeCosts, List.sum_append,
        topPairCompletionMergeCosts_sum]
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero,
        topPairCompletionCost]
      omega

/-! ## CPython final-collapse cost relation -/

/-- Source-faithful length-and-cost semantics of `merge_force_collapse`.

For at least three pending runs, `a`, `b`, and `c` are the final three lengths.
The strict source guard chooses the third-last pair exactly when `a < c`;
otherwise the top pair is merged. -/
inductive CPythonForceCollapseCost : List Nat → Nat → Prop
  | empty : CPythonForceCollapseCost [] 0
  | singleton (length : Nat) : CPythonForceCollapseCost [length] 0
  | pair (left right : Nat) :
      CPythonForceCollapseCost [left, right] (left + right)
  | mergeTop (before : List Nat) (a b c tailCost : Nat)
      (hselect : ¬a < c)
      (tail : CPythonForceCollapseCost (before ++ [a, b + c]) tailCost) :
      CPythonForceCollapseCost (before ++ [a, b, c]) (b + c + tailCost)
  | mergeThirdLast (before : List Nat) (a b c tailCost : Nat)
      (hselect : a < c)
      (tail : CPythonForceCollapseCost (before ++ [a + b, c]) tailCost) :
      CPythonForceCollapseCost (before ++ [a, b, c]) (a + b + tailCost)
