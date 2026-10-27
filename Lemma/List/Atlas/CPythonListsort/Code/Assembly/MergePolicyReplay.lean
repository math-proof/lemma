import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.CPythonListsort.Code.Assembly.MergePolicyReplay.Part4
open CPythonListsort CPythonListsort.PolicyEvent CPythonListsort.SpannedMergeTree


namespace CPythonListsort.PolicyEvent

/--
[formedSpans_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma formedSpans_nil
-- imply
  formedSpans [] = [] :=
-- proof
  rfl

end CPythonListsort.PolicyEvent

namespace CPythonListsort.PolicyEvent

/--
[formedSpans_formed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma formedSpans_formed
  {push : PendingPushEvent}
  {events : List PolicyEvent} :
-- imply
  formedSpans (.formed push :: events) = push.run :: formedSpans events :=
-- proof
  rfl

end CPythonListsort.PolicyEvent

namespace CPythonListsort.PolicyEvent

/--
[formedSpans_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma formedSpans_merge
  {event : LogicalMergeEvent}
  {events : List PolicyEvent} :
-- imply
  formedSpans (.merge event :: events) = formedSpans events :=
-- proof
  rfl

end CPythonListsort.PolicyEvent

namespace CPythonListsort.PolicyEvent

/--
[formedLengths_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma formedLengths_nil
-- imply
  formedLengths [] = [] :=
-- proof
  rfl

end CPythonListsort.PolicyEvent

namespace CPythonListsort.PolicyEvent

/--
[formedLengths_formed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma formedLengths_formed
  {push : PendingPushEvent}
  {events : List PolicyEvent} :
-- imply
  formedLengths (.formed push :: events) = push.run.len :: formedLengths events :=
-- proof
  rfl

end CPythonListsort.PolicyEvent

namespace CPythonListsort.PolicyEvent

/--
[formedLengths_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma formedLengths_merge
  {event : LogicalMergeEvent}
  {events : List PolicyEvent} :
-- imply
  formedLengths (.merge event :: events) = formedLengths events :=
-- proof
  rfl

end CPythonListsort.PolicyEvent

namespace CPythonListsort.PolicyEvent

/--
[logicalMergeCost_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma logicalMergeCost_nil
-- imply
  logicalMergeCost [] = 0 :=
-- proof
  rfl

end CPythonListsort.PolicyEvent

namespace CPythonListsort.PolicyEvent

/--
[logicalMergeCost_formed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma logicalMergeCost_formed
  {push : PendingPushEvent}
  {events : List PolicyEvent} :
-- imply
  logicalMergeCost (.formed push :: events) = logicalMergeCost events :=
-- proof
  rfl

end CPythonListsort.PolicyEvent

namespace CPythonListsort.PolicyEvent

/--
[logicalMergeCost_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma logicalMergeCost_merge
  {event : LogicalMergeEvent}
  {events : List PolicyEvent} :
-- imply
  logicalMergeCost (.merge event :: events) = event.left.len + event.right.len + logicalMergeCost events :=
-- proof
  rfl

end CPythonListsort.PolicyEvent

namespace CPythonListsort.PolicyEvent

/--
[logicalMergeCosts_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma logicalMergeCosts_nil
-- imply
  logicalMergeCosts [] = [] :=
-- proof
  rfl

end CPythonListsort.PolicyEvent

namespace CPythonListsort.PolicyEvent

/--
[logicalMergeCosts_formed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma logicalMergeCosts_formed
  {push : PendingPushEvent}
  {events : List PolicyEvent} :
-- imply
  logicalMergeCosts (.formed push :: events) = logicalMergeCosts events :=
-- proof
  rfl

end CPythonListsort.PolicyEvent

namespace CPythonListsort.PolicyEvent

/--
[logicalMergeCosts_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma logicalMergeCosts_merge
  {event : LogicalMergeEvent}
  {events : List PolicyEvent} :
-- imply
  logicalMergeCosts (.merge event :: events) = (event.left.len + event.right.len) :: logicalMergeCosts events :=
-- proof
  rfl

end CPythonListsort.PolicyEvent

namespace CPythonListsort.PolicyEvent

/--
[logicalMergeCosts_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma logicalMergeCosts_sum
  {events : List PolicyEvent} :
-- imply
  (logicalMergeCosts events).sum = logicalMergeCost events := by
-- proof
  induction events with
  | nil => rfl
  | cons event events ih =>
    cases event <;> simp [ih]

end CPythonListsort.PolicyEvent

namespace CPythonListsort.PolicyEvent

/--
[formedSpans_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma formedSpans_append
  {first second : List PolicyEvent} :
-- imply
  formedSpans (first ++ second) = formedSpans first ++ formedSpans second := by
-- proof
  induction first with
  | nil => rfl
  | cons event events ih =>
    cases event <;> simp [ih]

end CPythonListsort.PolicyEvent

namespace CPythonListsort.PolicyEvent

/--
[formedLengths_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma formedLengths_append
  {first second : List PolicyEvent} :
-- imply
  formedLengths (first ++ second) = formedLengths first ++ formedLengths second := by
-- proof
  simp [formedLengths, formedSpans_append, List.map_append]

end CPythonListsort.PolicyEvent

namespace CPythonListsort.PolicyEvent

/--
[logicalMergeCost_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma logicalMergeCost_append
  {first second : List PolicyEvent} :
-- imply
  logicalMergeCost (first ++ second) = logicalMergeCost first + logicalMergeCost second := by
-- proof
  induction first with
  | nil => simp
  | cons event events ih =>
    cases event <;> simp [ih, Nat.add_assoc]
/-! ## Forest invariants -/
namespace SpannedMergeTree

end CPythonListsort.PolicyEvent

namespace CPythonListsort.SpannedMergeTree

/--
[leaf_positive_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma leaf_positive_iff
  {span : RunSpan} :
-- imply
  (leaf span).Positive ↔ 0 < span.len := by
-- proof
  simp [Positive, leaf, MergeTree.runLengths]

end CPythonListsort.SpannedMergeTree

namespace CPythonListsort.SpannedMergeTree

/--
[merge_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma merge_positive
  {power : Nat}
  {left right : SpannedMergeTree}
-- given
  (hleft : left.Positive)
  (hright : right.Positive) :
-- imply
  (merge power left right).Positive := by
-- proof
  intro length hlength
  simp only [merge, MergeTree.runLengths, List.mem_append] at hlength
  exact hlength.elim (hleft length) (hright length)

end CPythonListsort.SpannedMergeTree

namespace CPythonListsort

/--
[forestRunLengths_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma forestRunLengths_nil
-- imply
  forestRunLengths [] = [] :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[forestRunLengths_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma forestRunLengths_cons
  {entry : SpannedMergeTree}
  {forest : List SpannedMergeTree} :
-- imply
  forestRunLengths (entry :: forest) = entry.tree.runLengths ++ forestRunLengths forest :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[forestMergeCost_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma forestMergeCost_nil
-- imply
  forestMergeCost [] = 0 :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[forestMergeCost_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma forestMergeCost_cons
  {entry : SpannedMergeTree}
  {forest : List SpannedMergeTree} :
-- imply
  forestMergeCost (entry :: forest) = entry.tree.mergeCost + forestMergeCost forest :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[applyPolicyEvent_merge_eq_some_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma applyPolicyEvent_merge_eq_some_iff
  {input : RunSpan}
  {forest result : List SpannedMergeTree}
  {event : LogicalMergeEvent} :
-- imply
  applyPolicyEvent? input forest (.merge event) = some result ↔ ∃ left right, forest[event.index]? = some left ∧ forest[event.index + 1]? = some right ∧ left.span = event.left ∧ right.span = event.right ∧ event.left.Adjacent event.right ∧ result = forest.take event.index ++ SpannedMergeTree.merge (replayBoundaryPower input event.left event.right) left right :: forest.drop (event.index + 2) := by
-- proof
  constructor
  · intro hresult
    cases hleft : forest[event.index]? with
    | none => simp [applyPolicyEvent?, hleft] at hresult
    | some left =>
      cases hright : forest[event.index + 1]? with
      | none => simp [applyPolicyEvent?, hleft, hright] at hresult
      | some right =>
        by_cases hcheck :
          left.span = event.left ∧ right.span = event.right ∧
            event.left.Adjacent event.right
        · have hout :
          forest.take event.index ++
            SpannedMergeTree.merge
              (replayBoundaryPower input event.left event.right)
              left right :: forest.drop (event.index + 2) = result := by
          simpa [applyPolicyEvent?, hleft, hright, hcheck] using hresult
          exact ⟨left, right, rfl, rfl, hcheck.1, hcheck.2.1,
            hcheck.2.2, hout.symm⟩
        · simp [applyPolicyEvent?, hleft, hright, hcheck] at hresult
  · rintro ⟨left, right, hleft, hright, hleftSpan, hrightSpan,
    hadjacent, rfl⟩
    simp [applyPolicyEvent?, hleft, hright, hleftSpan, hrightSpan, hadjacent]

end CPythonListsort

namespace CPythonListsort

/--
[replayPolicyEventsFrom_append_eq_some_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma replayPolicyEventsFrom_append_eq_some_iff
  {input : RunSpan}
  {forest result : List SpannedMergeTree}
  {first second : List PolicyEvent} :
-- imply
  replayPolicyEventsFrom? input forest (first ++ second) = some result ↔ ∃ middle, replayPolicyEventsFrom? input forest first = some middle ∧ replayPolicyEventsFrom? input middle second = some result := by
-- proof
  rw [replayPolicyEventsFrom_append]
  cases hfirst : replayPolicyEventsFrom? input forest first with
  | none => simp
  | some middle => simp

end CPythonListsort

namespace CPythonListsort

/--
[replayPolicyEvents_formedLengthRelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma replayPolicyEvents_formedLengthRelation
  {input : RunSpan}
  {events : List PolicyEvent}
  {result : List SpannedMergeTree}
-- given
  (hreplay : replayPolicyEvents? input events = some result) :
-- imply
  ∀ push, .formed push ∈ events → FormedLengthRelation push :=
-- proof
replayPolicyEventsFrom_formedLengthRelation hreplay

end CPythonListsort

namespace CPythonListsort

/--
[normalizePolicyForest_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma normalizePolicyForest_empty
  {base : Nat} :
-- imply
  normalizePolicyForest? { base := base, len := 0 } [] = some .empty := by
-- proof
  simp [normalizePolicyForest?]

end CPythonListsort

namespace CPythonListsort

/--
[replayMergePlan_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma replayMergePlan_empty
  {base : Nat} :
-- imply
  replayMergePlan? { base := base, len := 0 } [] = some .empty := by
-- proof
  simp [replayMergePlan?, replayPolicyEvents?, replayPolicyEventsFrom?]

end CPythonListsort

namespace CPythonListsort

/--
[normalizePolicyForest_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma normalizePolicyForest_singleton
  {input : RunSpan}
  {root : SpannedMergeTree}
-- given
  (hspan : root.span = input) :
-- imply
  normalizePolicyForest? input [root] = some (.tree root.tree) := by
-- proof
  simp [normalizePolicyForest?, hspan]

end CPythonListsort

namespace CPythonListsort

/--
[forestRunLengths_append_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
private lemma forestRunLengths_append_leaf
  (forest : List SpannedMergeTree) (span : RunSpan) :
  forestRunLengths (forest ++ [SpannedMergeTree.leaf span]) =
    forestRunLengths forest ++ [span.len] := by
  simp [forestRunLengths, SpannedMergeTree.leaf, MergeTree.runLengths]

end CPythonListsort

namespace CPythonListsort

/--
[forestMergeCost_append_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
private lemma forestMergeCost_append_leaf
  (forest : List SpannedMergeTree) (span : RunSpan) :
  forestMergeCost (forest ++ [SpannedMergeTree.leaf span]) =
    forestMergeCost forest := by
  simp [forestMergeCost, SpannedMergeTree.leaf, MergeTree.mergeCost]

end CPythonListsort

namespace CPythonListsort

/--
[list_eq_take_append_get_drop_of_getElem?_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
keeps all index arithmetic local to replay and lets downstream users consume
the semantic equalities without reopening the implementation. -/
private lemma list_eq_take_append_get_drop_of_getElem?_eq_some
  {xs : List α} {i : Nat} {x : α} (h : xs[i]? = some x) :
  xs = xs.take i ++ x :: xs.drop (i + 1) := by
  have hi : i < xs.length := (List.getElem?_eq_some_iff.mp h).1
  have hdrop : xs.drop i = x :: xs.drop (i + 1) := by
    have hx : xs[i] = x := by
      simpa [List.getElem?_eq_getElem hi] using h
    rw [List.drop_eq_getElem_cons hi, hx]
  calc
    xs = xs.take i ++ xs.drop i := (List.take_append_drop i xs).symm
    _ = xs.take i ++ x :: xs.drop (i + 1) := by rw [hdrop]

end CPythonListsort

namespace CPythonListsort

/--
[replay_merge_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
private lemma replay_merge_decomposition
  {forest : List SpannedMergeTree} {event : LogicalMergeEvent}
  {left right : SpannedMergeTree}
  (hleft : forest[event.index]? = some left)
  (hright : forest[event.index + 1]? = some right) :
  forest = forest.take event.index ++
    left :: right :: forest.drop (event.index + 2) := by
  obtain ⟨hi, hleftEq⟩ := List.getElem?_eq_some_iff.mp hleft
  obtain ⟨hiOne, hrightEq⟩ := List.getElem?_eq_some_iff.mp hright
  calc
    forest = forest.take event.index ++ forest.drop event.index :=
      (List.take_append_drop event.index forest).symm
    _ = forest.take event.index ++
      forest[event.index] :: forest.drop (event.index + 1) := by
      rw [List.drop_eq_getElem_cons hi]
    _ = forest.take event.index ++
      left :: forest.drop (event.index + 1) := by rw [hleftEq]
    _ = forest.take event.index ++ left ::
      forest[event.index + 1] :: forest.drop (event.index + 2) := by
      rw [List.drop_eq_getElem_cons hiOne]
    _ = forest.take event.index ++
      left :: right :: forest.drop (event.index + 2) := by rw [hrightEq]

end CPythonListsort

namespace CPythonListsort

/--
[forestRunLengths_merge_splice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
private lemma forestRunLengths_merge_splice
  (before after : List SpannedMergeTree)
  (left right : SpannedMergeTree) (power : Nat) :
  forestRunLengths
    (before ++ SpannedMergeTree.merge power left right :: after) =
    forestRunLengths (before ++ left :: right :: after) := by
  simp [forestRunLengths, SpannedMergeTree.merge, MergeTree.runLengths,
    List.append_assoc]

end CPythonListsort

namespace CPythonListsort

/--
[forestMergeCost_merge_splice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
private lemma forestMergeCost_merge_splice
  (before after : List SpannedMergeTree)
  (left right : SpannedMergeTree) (power : Nat) :
  forestMergeCost
    (before ++ SpannedMergeTree.merge power left right :: after) =
    forestMergeCost (before ++ left :: right :: after) +
      left.tree.totalLength + right.tree.totalLength := by
  simp [forestMergeCost, SpannedMergeTree.merge, MergeTree.mergeCost]
  omega

end CPythonListsort

namespace CPythonListsort

/--
[applyPolicyEvent_runLengths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma applyPolicyEvent_runLengths
  {input : RunSpan}
  {forest result : List SpannedMergeTree}
  {event : PolicyEvent}
-- given
  (hreplay : applyPolicyEvent? input forest event = some result) :
-- imply
  forestRunLengths result = forestRunLengths forest ++ PolicyEvent.formedLengths [event] := by
-- proof
  cases event with
  | formed push =>
    simp only [applyPolicyEvent?] at hreplay
    split at hreplay
    · have hresult := Option.some.inj hreplay
      subst result
      exact forestRunLengths_append_leaf forest push.run
    · simp at hreplay
  | merge event =>
    rcases (applyPolicyEvent_merge_eq_some_iff input forest result event).mp
      hreplay with
      ⟨left, right, hleft, hright, _, _, _, hresult⟩
    subst result
    rw [forestRunLengths_merge_splice]
    simp only [PolicyEvent.formedLengths_merge,
      PolicyEvent.formedLengths_nil, List.append_nil]
    exact congrArg forestRunLengths
      (replay_merge_decomposition hleft hright).symm

end CPythonListsort

namespace CPythonListsort

/--
[applyPolicyEvent_cost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma applyPolicyEvent_cost
  {input : RunSpan}
  {forest result : List SpannedMergeTree}
  {event : PolicyEvent}
-- given
  (hinv : PolicyForestInv input forest)
  (hreplay : applyPolicyEvent? input forest event = some result) :
-- imply
  forestMergeCost result = forestMergeCost forest + PolicyEvent.logicalMergeCost [event] := by
-- proof
  cases event with
  | formed push =>
    simp only [applyPolicyEvent?] at hreplay
    split at hreplay
    · have hresult := Option.some.inj hreplay
      subst result
      exact forestMergeCost_append_leaf forest push.run
    · simp at hreplay
  | merge event =>
    rcases (applyPolicyEvent_merge_eq_some_iff input forest result event).mp
      hreplay with
      ⟨left, right, hleft, hright, hleftSpan, hrightSpan, _, hresult⟩
    subst result
    rcases List.getElem?_eq_some_iff.mp hleft with
      ⟨hleftBound, hleftEq⟩
    rcases List.getElem?_eq_some_iff.mp hright with
      ⟨hrightBound, hrightEq⟩
    have hleftMem : left ∈ forest :=
      List.mem_iff_getElem.mpr
        ⟨event.index, hleftBound, hleftEq⟩
    have hrightMem : right ∈ forest :=
      List.mem_iff_getElem.mpr
        ⟨event.index + 1, hrightBound, hrightEq⟩
    have hleftValid := (hinv.1 left hleftMem).1
    have hrightValid := (hinv.1 right hrightMem).1
    rw [forestMergeCost_merge_splice]
    have hdecompCost := congrArg forestMergeCost
      (replay_merge_decomposition hleft hright)
    rw [← hdecompCost]
    simp only [PolicyEvent.logicalMergeCost_merge,
      PolicyEvent.logicalMergeCost_nil, Nat.add_zero]
    simp only [SpannedMergeTree.Valid] at hleftValid hrightValid
    rw [hleftValid, hrightValid, hleftSpan, hrightSpan]
    omega

end CPythonListsort

namespace CPythonListsort

/--
[adjacentForest_append_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemmas. -/
private lemma adjacentForest_append_leaf
  {input : RunSpan} {forest : List SpannedMergeTree}
  {push : PendingPushEvent}
  (hadj : AdjacentForest forest)
  (hbase : push.run.base = nextForestBase input forest) :
  AdjacentForest (forest ++ [SpannedMergeTree.leaf push.run]) := by
  induction forest with
  | nil => simp [AdjacentForest]
  | cons first rest ih =>
    cases rest with
    | nil =>
      have hbase' : push.run.base = first.span.endIndex := by
        simpa [nextForestBase] using hbase
      change first.span.Adjacent (SpannedMergeTree.leaf push.run).span ∧ True
      constructor
      · change first.span.Adjacent push.run
        exact hbase'.symm
      · trivial
    | cons second tail =>
      simp only [AdjacentForest] at hadj ⊢
      exact ⟨hadj.1, ih hadj.2 hbase⟩

end CPythonListsort

namespace CPythonListsort

/--
[policyForestInv_append_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
private lemma policyForestInv_append_leaf
  {input : RunSpan} {forest : List SpannedMergeTree}
  {push : PendingPushEvent}
  (hinv : PolicyForestInv input forest)
  (hvalid : ValidFormedEvent input forest push) :
  PolicyForestInv input (forest ++ [SpannedMergeTree.leaf push.run]) := by
  obtain ⟨htrees, hadj, hstarts, hwithin⟩ := hinv
  rcases hvalid with
    ⟨_, hbase, hremaining, hpositive, hlenRemaining, _⟩
  refine ⟨?_, adjacentForest_append_leaf hadj hbase, ?_, ?_⟩
  · intro entry hentry
    rw [List.mem_append] at hentry
    obtain hentry | hentry := hentry
    · exact htrees entry hentry
    · simp only [List.mem_singleton] at hentry
      subst entry
      exact ⟨SpannedMergeTree.leaf_valid push.run,
        (SpannedMergeTree.leaf_positive_iff push.run).2 hpositive⟩
  · cases forest with
    | nil => simpa [ForestStartsAt, nextForestBase,
      SpannedMergeTree.leaf] using hbase
    | cons first rest => simpa [ForestStartsAt] using hstarts
  · intro entry hentry
    rw [List.mem_append] at hentry
    obtain hentry | hentry := hentry
    · exact hwithin entry hentry
    · simp only [List.mem_singleton] at hentry
      subst entry
      simp only [SpannedMergeTree.leaf]
      rw [RunSpan.endIndex]
      omega

end CPythonListsort

namespace CPythonListsort

/--
[span_adjacent_merge_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
private lemma span_adjacent_merge_left
  (power : Nat) {before left right : SpannedMergeTree}
  (h : before.span.Adjacent left.span) :
  before.span.Adjacent (SpannedMergeTree.merge power left right).span := by
  unfold RunSpan.Adjacent at h ⊢
  change before.span.endIndex = left.span.base at h
  change before.span.endIndex = left.span.base
  exact h

end CPythonListsort

namespace CPythonListsort

/--
[span_merge_adjacent_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
private lemma span_merge_adjacent_right
  (power : Nat) {left right after : SpannedMergeTree}
  (hlr : left.span.Adjacent right.span)
  (hra : right.span.Adjacent after.span) :
  (SpannedMergeTree.merge power left right).span.Adjacent after.span := by
  unfold RunSpan.Adjacent RunSpan.endIndex at hlr hra ⊢
  change left.span.base + (left.span.len + right.span.len) = after.span.base
  change left.span.base + left.span.len = right.span.base at hlr
  change right.span.base + right.span.len = after.span.base at hra
  omega

end CPythonListsort

namespace CPythonListsort

/--
[span_merge_endIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
private lemma span_merge_endIndex
  (power : Nat) {left right : SpannedMergeTree}
  (hlr : left.span.Adjacent right.span) :
  (SpannedMergeTree.merge power left right).span.endIndex =
    right.span.endIndex := by
  change left.span.base + (left.span.len + right.span.len) =
    right.span.base + right.span.len
  unfold RunSpan.Adjacent RunSpan.endIndex at hlr
  change left.span.base + left.span.len = right.span.base at hlr
  omega

end CPythonListsort

namespace CPythonListsort

/--
[adjacentForest_merge_splice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
private lemma adjacentForest_merge_splice
  (power : Nat) (before after : List SpannedMergeTree)
  (left right : SpannedMergeTree)
  (hadj : AdjacentForest (before ++ left :: right :: after))
  (hlr : left.span.Adjacent right.span) :
  AdjacentForest
    (before ++ SpannedMergeTree.merge power left right :: after) := by
  induction before with
  | nil =>
    cases after with
    | nil => simp [AdjacentForest]
    | cons next tail =>
      simp only [List.nil_append, AdjacentForest] at hadj ⊢
      exact ⟨span_merge_adjacent_right power hlr hadj.2.1, hadj.2.2⟩
  | cons first before ih =>
    cases before with
    | nil =>
      simp only [List.cons_append, List.nil_append, AdjacentForest] at hadj ⊢
      refine ⟨span_adjacent_merge_left power hadj.1, ?_⟩
      cases after with
      | nil => simp [AdjacentForest]
      | cons next tail =>
        exact ⟨span_merge_adjacent_right power hlr hadj.2.2.1,
          hadj.2.2.2⟩
    | cons second tail =>
      simp only [List.cons_append, AdjacentForest] at hadj ⊢
      exact ⟨hadj.1, ih hadj.2⟩

end CPythonListsort

namespace CPythonListsort

/--
[policyForestInv_merge_splice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
private lemma policyForestInv_merge_splice
  {input : RunSpan} {before after : List SpannedMergeTree}
  {left right : SpannedMergeTree} {power : Nat}
  (hinv : PolicyForestInv input (before ++ left :: right :: after))
  (hadjacent : left.span.Adjacent right.span) :
  PolicyForestInv input
    (before ++ SpannedMergeTree.merge power left right :: after) := by
  obtain ⟨htrees, hadj, hstarts, hwithin⟩ := hinv
  have hleftMem : left ∈ before ++ left :: right :: after := by simp
  have hrightMem : right ∈ before ++ left :: right :: after := by simp
  have hleft := htrees left hleftMem
  have hright := htrees right hrightMem
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro entry hentry
    simp only [List.mem_append, List.mem_cons] at hentry
    obtain hbefore | hmerged | hafter := hentry
    · exact htrees entry (by simp [hbefore])
    · subst entry
      exact ⟨SpannedMergeTree.merge_valid power hleft.1 hright.1,
        SpannedMergeTree.merge_positive power hleft.2 hright.2⟩
    · exact htrees entry (by simp [hafter])
  · exact adjacentForest_merge_splice power before after left right hadj hadjacent
  · cases before with
    | nil => simpa [ForestStartsAt, SpannedMergeTree.merge, RunSpan.merge] using hstarts
    | cons first rest => simpa [ForestStartsAt] using hstarts
  · intro entry hentry
    simp only [List.mem_append, List.mem_cons] at hentry
    obtain hbefore | hmerged | hafter := hentry
    · exact hwithin entry (by simp [hbefore])
    · subst entry
      have hrightWithin := hwithin right hrightMem
      rwa [span_merge_endIndex power hadjacent]
    · exact hwithin entry (by simp [hafter])

end CPythonListsort

namespace CPythonListsort

/--
[applyPolicyEvent_preserves_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma applyPolicyEvent_preserves_inv
  {input : RunSpan}
  {forest result : List SpannedMergeTree}
  {event : PolicyEvent}
-- given
  (hinv : PolicyForestInv input forest)
  (hreplay : applyPolicyEvent? input forest event = some result) :
-- imply
  PolicyForestInv input result := by
-- proof
  cases event with
  | formed push =>
    simp only [applyPolicyEvent?] at hreplay
    split at hreplay
    · rename_i hvalid
      simp only [Option.some.injEq] at hreplay
      subst result
      exact policyForestInv_append_leaf hinv hvalid
    · simp at hreplay
  | merge event =>
    rcases (applyPolicyEvent_merge_eq_some_iff input forest result event).mp
      hreplay with
      ⟨left, right, hleft, hright, hleftSpan, hrightSpan,
        heventAdjacent, hresult⟩
    subst result
    rw [replay_merge_decomposition hleft hright] at hinv
    have hactual : left.span.Adjacent right.span := by
      rwa [hleftSpan, hrightSpan]
    exact policyForestInv_merge_splice
      (power := replayBoundaryPower input event.left event.right)
      hinv hactual

end CPythonListsort

namespace CPythonListsort

/--
[replayPolicyEventsFrom_runLengths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma replayPolicyEventsFrom_runLengths
  {input : RunSpan}
  {initial result : List SpannedMergeTree}
  {events : List PolicyEvent}
-- given
  (hreplay : replayPolicyEventsFrom? input initial events = some result) :
-- imply
  forestRunLengths result = forestRunLengths initial ++ PolicyEvent.formedLengths events := by
-- proof
  induction events generalizing initial with
  | nil =>
    simp only [replayPolicyEventsFrom?, Option.some.injEq] at hreplay
    subst result
    simp
  | cons event events ih =>
    simp only [replayPolicyEventsFrom?] at hreplay
    cases hstep : applyPolicyEvent? input initial event with
    | none => simp [hstep] at hreplay
    | some middle =>
      rw [hstep] at hreplay
      have hfirst := applyPolicyEvent_runLengths hstep
      have hrest := ih hreplay
      rw [hrest, hfirst]
      cases event <;> simp [List.append_assoc]

end CPythonListsort

namespace CPythonListsort

/--
[replayPolicyEventsFrom_preserves_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma replayPolicyEventsFrom_preserves_inv
  {input : RunSpan}
  {initial result : List SpannedMergeTree}
  {events : List PolicyEvent}
-- given
  (hinv : PolicyForestInv input initial)
  (hreplay : replayPolicyEventsFrom? input initial events = some result) :
-- imply
  PolicyForestInv input result := by
-- proof
  induction events generalizing initial with
  | nil =>
    simp only [replayPolicyEventsFrom?, Option.some.injEq] at hreplay
    subst result
    exact hinv
  | cons event events ih =>
    simp only [replayPolicyEventsFrom?] at hreplay
    cases hstep : applyPolicyEvent? input initial event with
    | none => simp [hstep] at hreplay
    | some middle =>
      rw [hstep] at hreplay
      exact ih (applyPolicyEvent_preserves_inv hinv hstep) hreplay

end CPythonListsort

namespace CPythonListsort

/--
[replayPolicyEventsFrom_cost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma replayPolicyEventsFrom_cost
  {input : RunSpan}
  {initial result : List SpannedMergeTree}
  {events : List PolicyEvent}
-- given
  (hinv : PolicyForestInv input initial)
  (hreplay : replayPolicyEventsFrom? input initial events = some result) :
-- imply
  forestMergeCost result = forestMergeCost initial + PolicyEvent.logicalMergeCost events := by
-- proof
  induction events generalizing initial with
  | nil =>
    simp only [replayPolicyEventsFrom?, Option.some.injEq] at hreplay
    subst result
    simp
  | cons event events ih =>
    simp only [replayPolicyEventsFrom?] at hreplay
    cases hstep : applyPolicyEvent? input initial event with
    | none => simp [hstep] at hreplay
    | some middle =>
      rw [hstep] at hreplay
      have hmiddle := applyPolicyEvent_preserves_inv hinv hstep
      have hfirst := applyPolicyEvent_cost hinv hstep
      have hrest := ih hmiddle hreplay
      rw [hrest, hfirst]
      cases event <;> simp
      omega

end CPythonListsort

namespace CPythonListsort

/--
[policyForestInv_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma policyForestInv_empty
  {input : RunSpan} :
-- imply
  PolicyForestInv input [] := by
-- proof
  simp [PolicyForestInv, AdjacentForest, ForestStartsAt, ForestWithin]

end CPythonListsort

namespace CPythonListsort

/--
[replayPolicyEvents_preserves_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma replayPolicyEvents_preserves_partition
  {input : RunSpan}
  {events : List PolicyEvent}
  {result : List SpannedMergeTree}
-- given
  (hreplay : replayPolicyEvents? input events = some result) :
-- imply
  PolicyForestInv input result :=
-- proof
replayPolicyEventsFrom_preserves_inv (policyForestInv_empty input) hreplay

end CPythonListsort

namespace CPythonListsort

/--
[replayPolicyEvents_runLengths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma replayPolicyEvents_runLengths
  {input : RunSpan}
  {events : List PolicyEvent}
  {result : List SpannedMergeTree}
-- given
  (hreplay : replayPolicyEvents? input events = some result) :
-- imply
  forestRunLengths result = PolicyEvent.formedLengths events := by
-- proof
  simpa [replayPolicyEvents?, forestRunLengths] using
    replayPolicyEventsFrom_runLengths hreplay

end CPythonListsort

namespace CPythonListsort

/--
[replayPolicyEvents_cost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma replayPolicyEvents_cost
  {input : RunSpan}
  {events : List PolicyEvent}
  {result : List SpannedMergeTree}
-- given
  (hreplay : replayPolicyEvents? input events = some result) :
-- imply
  forestMergeCost result = PolicyEvent.logicalMergeCost events := by
-- proof
  simpa [replayPolicyEvents?, forestMergeCost] using
    replayPolicyEventsFrom_cost (policyForestInv_empty input) hreplay

end CPythonListsort

namespace CPythonListsort

/--
[completePolicyReplay_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma completePolicyReplay_exact
  {input : RunSpan}
  {events : List PolicyEvent}
  {root : SpannedMergeTree}
-- given
  (hreplay : replayPolicyEvents? input events = some [root]) :
-- imply
  root.tree.runLengths = PolicyEvent.formedLengths events ∧ root.tree.mergeCost = PolicyEvent.logicalMergeCost events := by
-- proof
  constructor
  · simpa [forestRunLengths] using replayPolicyEvents_runLengths hreplay
  · simpa [forestMergeCost] using replayPolicyEvents_cost hreplay

end CPythonListsort

namespace CPythonListsort

/--
[replayMergePlan_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
lemma replayMergePlan_exact
  {input : RunSpan}
  {events : List PolicyEvent}
  {plan : MergePlan}
-- given
  (hreplay : replayMergePlan? input events = some plan) :
-- imply
  plan.runLengths = PolicyEvent.formedLengths events ∧ plan.mergeCost = PolicyEvent.logicalMergeCost events := by
-- proof
  unfold replayMergePlan? at hreplay
  cases hforest : replayPolicyEvents? input events with
  | none => simp [hforest] at hreplay
  | some forest =>
    rw [hforest] at hreplay
    cases forest with
    | nil =>
      change (if input.len = 0 then some .empty else none) = some plan at hreplay
      split at hreplay
      · simp only [Option.some.injEq] at hreplay
        subst plan
        have hlengths := replayPolicyEvents_runLengths hforest
        have hcost := replayPolicyEvents_cost hforest
        simpa [forestRunLengths, forestMergeCost, MergePlan.runLengths,
          MergePlan.mergeCost] using And.intro hlengths hcost
      · simp at hreplay
    | cons root rest =>
      cases rest with
      | nil =>
        change (if root.span = input then some (.tree root.tree) else none) =
          some plan at hreplay
        split at hreplay
        · simp only [Option.some.injEq] at hreplay
          subst plan
          exact completePolicyReplay_exact hforest
        · simp at hreplay
      | cons second tail => simp [normalizePolicyForest?] at hreplay

end CPythonListsort

/--
[applyPolicyEvent_formed_eq_some_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
private lemma applyPolicyEvent_formed_eq_some_iff_eq
  {input : RunSpan}
  {forest result : List SpannedMergeTree}
  {push : PendingPushEvent} :
-- imply
  applyPolicyEvent? input forest (.formed push) = some result ↔ ValidFormedEvent input forest push ∧ result = forest ++ [SpannedMergeTree.leaf push.run] := by
-- proof
  apply CPythonListsort.applyPolicyEvent_formed_eq_some_iff input forest result push

/--
[replayPolicyEventsFrom_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
private lemma replayPolicyEventsFrom_append_eq
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {first second : List PolicyEvent} :
-- imply
  replayPolicyEventsFrom? input forest (first ++ second) = (replayPolicyEventsFrom? input forest first).bind fun middle => replayPolicyEventsFrom? input middle second := by
-- proof
  apply CPythonListsort.replayPolicyEventsFrom_append input forest first second

/--
[replayPolicyEventsFrom_formedLengthRelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/MergePolicyReplay.lean)
-/
@[path]
private lemma replayPolicyEventsFrom_formedLengthRelation_eq
  {input : RunSpan}
  {initial result : List SpannedMergeTree}
  {events : List PolicyEvent}
-- given
  (hreplay : replayPolicyEventsFrom? input initial events = some result) :
-- imply
  ∀ push, .formed push ∈ events → FormedLengthRelation push := by
-- proof
  apply CPythonListsort.replayPolicyEventsFrom_formedLengthRelation hreplay


-- created on 2026-10-23
