/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.MergeTreeCost
import sympy.atlas.CPythonListsort.Code.Transcription.Powerloop
import Mathlib.Tactic

/-!
# Checked replay of the interleaved PowerSort policy trace

The access trace records formed-run pushes and logical, pre-trimming merges in
one chronological channel.  This module gives that raw channel a deliberately
strict, pure semantics.  A formed-run observation is accepted only when its
post-push depth, source interval, adaptive-minrun branch, and remaining-input
metadata agree.  A merge is accepted only when its index and full source
spans identify an adjacent pair in the current forest.

Every replayed internal node is labelled by the transcribed `powerloop`
applied to the aggregate spans being merged.  No label supplied by the trace
is trusted, and physical trimming does not alter the logical merge cost.
-/

namespace CPythonListsort

/-! ## Raw event projections -/

namespace PolicyEvent

/-- The source spans of formed runs, in chronological order. -/
def formedSpans : List PolicyEvent → List RunSpan
  | [] => []
  | .formed push :: events => push.run :: formedSpans events
  | .merge _ :: events => formedSpans events

/-- The lengths of formed runs, in chronological order. -/
def formedLengths (events : List PolicyEvent) : List Nat :=
  (formedSpans events).map RunSpan.len

/-- Paper merge cost accumulated by the logical pre-trimming merge events. -/
def logicalMergeCost : List PolicyEvent → Nat
  | [] => 0
  | .formed _ :: events => logicalMergeCost events
  | .merge event :: events =>
      event.left.len + event.right.len + logicalMergeCost events

/-- The individual pre-trimming merge costs, in chronological event order.

This projection is deliberately separate from `logicalMergeCost`: executable
regressions can pin a concrete merge schedule rather than only its total. -/
def logicalMergeCosts : List PolicyEvent → List Nat
  | [] => []
  | .formed _ :: events => logicalMergeCosts events
  | .merge event :: events =>
      (event.left.len + event.right.len) :: logicalMergeCosts events

/-- Every leaf has positive length. -/
def Positive (entry : SpannedMergeTree) : Prop :=
  ∀ length ∈ entry.tree.runLengths, 0 < length

/-- Root spans in a forest are consecutive from left to right. -/
def AdjacentForest : List SpannedMergeTree → Prop
  | [] => True
  | [_] => True
  | left :: right :: rest =>
      left.span.Adjacent right.span ∧ AdjacentForest (right :: rest)

/-- The first root of a nonempty forest starts at `input.base`. -/
def ForestStartsAt (input : RunSpan) : List SpannedMergeTree → Prop
  | [] => True
  | first :: _ => first.span.base = input.base

/-- Every represented interval ends within the declared input interval. -/
def ForestWithin (input : RunSpan) (forest : List SpannedMergeTree) : Prop :=
  ∀ entry ∈ forest, entry.span.endIndex ≤ input.endIndex

/-- Replay invariant: valid positive trees forming an adjacent input prefix. -/
def PolicyForestInv (input : RunSpan)
    (forest : List SpannedMergeTree) : Prop :=
  (∀ entry ∈ forest, entry.Valid ∧ entry.Positive) ∧
    AdjacentForest forest ∧
    ForestStartsAt input forest ∧
    ForestWithin input forest

/-- Flatten the leaf lengths of an ordered merge forest. -/
def forestRunLengths (forest : List SpannedMergeTree) : List Nat :=
  forest.flatMap fun entry => entry.tree.runLengths

/-- Sum the already-incurred internal merge cost of a forest. -/
def forestMergeCost (forest : List SpannedMergeTree) : Nat :=
  (forest.map fun entry => entry.tree.mergeCost).sum

/-! ## Checked event semantics -/

/-- Exact adaptive-minrun relationship recorded by a formed-run event.

The first disjunct is the `naturalLength < target` branch: `binarysort`
extends the run to `min remainingBefore target`.  The second is the already
long natural-run branch, where the final run length is unchanged. -/
def FormedLengthRelation (push : PendingPushEvent) : Prop :=
  0 < push.naturalLength ∧
    push.naturalLength ≤ push.remainingBefore ∧
    0 < push.target ∧
    ((push.naturalLength < push.target ∧
        push.run.len = min push.remainingBefore push.target) ∨
      (push.target ≤ push.naturalLength ∧
        push.run.len = push.naturalLength))

instance (push : PendingPushEvent) : Decidable (FormedLengthRelation push) :=
  inferInstanceAs (Decidable
    (0 < push.naturalLength ∧ push.naturalLength ≤ push.remainingBefore ∧
      0 < push.target ∧
      ((push.naturalLength < push.target ∧
          push.run.len = min push.remainingBefore push.target) ∨
        (push.target ≤ push.naturalLength ∧
          push.run.len = push.naturalLength))))

/-- The base at which a new formed run must begin. -/
def nextForestBase (input : RunSpan)
    (forest : List SpannedMergeTree) : Nat :=
  match forest.getLast? with
  | none => input.base
  | some last => last.span.endIndex

/-- Full validation predicate for a formed-run event at one replay point. -/
def ValidFormedEvent (input : RunSpan) (forest : List SpannedMergeTree)
    (push : PendingPushEvent) : Prop :=
  push.depthAfter = forest.length + 1 ∧
    push.run.base = nextForestBase input forest ∧
    push.run.base + push.remainingBefore = input.endIndex ∧
    0 < push.run.len ∧
    push.run.len ≤ push.remainingBefore ∧
    FormedLengthRelation push

instance (input : RunSpan) (forest : List SpannedMergeTree)
    (push : PendingPushEvent) : Decidable (ValidFormedEvent input forest push) :=
  inferInstanceAs (Decidable
    (push.depthAfter = forest.length + 1 ∧
      push.run.base = nextForestBase input forest ∧
      push.run.base + push.remainingBefore = input.endIndex ∧
      0 < push.run.len ∧ push.run.len ≤ push.remainingBefore ∧
      FormedLengthRelation push))

/-- The exact transcribed node power belonging to two aggregate spans. -/
def replayBoundaryPower (input left right : RunSpan) : Nat :=
  powerloop (BitVec.ofNat 64 (left.base - input.base))
    (BitVec.ofNat 64 left.len) (BitVec.ofNat 64 right.len)
    (BitVec.ofNat 64 input.len)

/-- Apply one raw policy event to an ordered merge forest.

Formed-run metadata is checked before appending a leaf.  A merge checks both
pre-trim operand spans at the recorded index and checks adjacency before
splicing in a node labelled by `replayBoundaryPower`. -/
def applyPolicyEvent? (input : RunSpan)
    (forest : List SpannedMergeTree) :
    PolicyEvent → Option (List SpannedMergeTree)
  | .formed push =>
      if ValidFormedEvent input forest push then
        some (forest ++ [SpannedMergeTree.leaf push.run])
      else
        none
  | .merge event => do
      let left ← forest[event.index]?
      let right ← forest[event.index + 1]?
      if left.span = event.left ∧ right.span = event.right ∧
          event.left.Adjacent event.right then
        some (forest.take event.index ++
          SpannedMergeTree.merge
            (replayBoundaryPower input event.left event.right) left right ::
          forest.drop (event.index + 2))
      else
        none

/-- Replay a chronological, interleaved policy-event stream. -/
def replayPolicyEventsFrom? (input : RunSpan) :
    List SpannedMergeTree → List PolicyEvent →
      Option (List SpannedMergeTree)
  | forest, [] => some forest
  | forest, event :: events => do
      let forest ← applyPolicyEvent? input forest event
      replayPolicyEventsFrom? input forest events

/-- Replay a complete policy stream from the empty initial forest. -/
def replayPolicyEvents? (input : RunSpan)
    (events : List PolicyEvent) : Option (List SpannedMergeTree) :=
  replayPolicyEventsFrom? input [] events

/-- Exact success characterization for one formed-run event. -/
theorem applyPolicyEvent_formed_eq_some_iff
    (input : RunSpan) (forest result : List SpannedMergeTree)
    (push : PendingPushEvent) :
    applyPolicyEvent? input forest (.formed push) = some result ↔
      ValidFormedEvent input forest push ∧
        result = forest ++ [SpannedMergeTree.leaf push.run] := by
  simp [applyPolicyEvent?, eq_comm]

/-- Replaying concatenated event segments is exactly sequential replay. -/
theorem replayPolicyEventsFrom_append (input : RunSpan)
    (forest : List SpannedMergeTree) (first second : List PolicyEvent) :
    replayPolicyEventsFrom? input forest (first ++ second) =
      (replayPolicyEventsFrom? input forest first).bind fun middle =>
        replayPolicyEventsFrom? input middle second := by
  induction first generalizing forest with
  | nil => rfl
  | cons event events ih =>
      simp only [List.cons_append, replayPolicyEventsFrom?]
      cases hstep : applyPolicyEvent? input forest event with
      | none => simp
      | some middle => simpa using ih middle

/-- Every formed-run observation accepted by a successful replay satisfies
the exact adaptive-minrun branch equation recorded in that observation.  This
exports the arithmetic check performed by `applyPolicyEvent?`; downstream
cost theorems therefore need not treat the trace metadata as trusted prose. -/
theorem replayPolicyEventsFrom_formedLengthRelation
    {input : RunSpan} {initial result : List SpannedMergeTree}
    {events : List PolicyEvent}
    (hreplay : replayPolicyEventsFrom? input initial events = some result) :
    ∀ push, .formed push ∈ events → FormedLengthRelation push := by
  induction events generalizing initial with
  | nil => simp
  | cons event events ih =>
      simp only [replayPolicyEventsFrom?] at hreplay
      cases hstep : applyPolicyEvent? input initial event with
      | none => simp [hstep] at hreplay
      | some middle =>
          rw [hstep] at hreplay
          intro push hpush
          simp only [List.mem_cons] at hpush
          rcases hpush with hhead | htail
          · cases event with
            | formed observed =>
                cases hhead
                exact
                  ((applyPolicyEvent_formed_eq_some_iff input initial middle
                    push).mp hstep).1.2.2.2.2.2
            | merge observed => contradiction
          · exact ih hreplay push htail

/-! ## Empty/single-root normalization -/

/-- Normalize a completed forest to the paper-facing empty-or-tree plan.

The empty forest is accepted only for an empty input.  A singleton is accepted
only when its root span is exactly the declared input span. -/
def normalizePolicyForest? (input : RunSpan) :
    List SpannedMergeTree → Option MergePlan
  | [] => if input.len = 0 then some .empty else none
  | [root] => if root.span = input then some (.tree root.tree) else none
  | _ => none

/-- Replay and normalize one complete policy trace. -/
def replayMergePlan? (input : RunSpan)
    (events : List PolicyEvent) : Option MergePlan := do
  let forest ← replayPolicyEvents? input events
  normalizePolicyForest? input forest
