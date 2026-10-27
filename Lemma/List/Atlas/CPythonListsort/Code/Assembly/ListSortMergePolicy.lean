import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.CPythonListsort.Code.Assembly.ListSortMergePolicy
open CPythonListsort
open forest at the exact reached final-collapse boundary. -/


namespace CPythonListsort

/--
[replayTopLevelMergePlan_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma replayTopLevelMergePlan_empty
  {κ : Type u}
  {ν : Type v}
  {base : Nat} :
-- imply
  replayTopLevelMergePlan? { base := base, len := 0 } [] = some .empty := by
-- proof
  simp [replayTopLevelMergePlan?]

end CPythonListsort

namespace CPythonListsort

/--
[replayTopLevelMergePlan_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma replayTopLevelMergePlan_singleton
  {κ : Type u}
  {ν : Type v}
  {base : Nat} :
-- imply
  replayTopLevelMergePlan? { base := base, len := 1 } [] = some (.tree (.leaf 1)) := by
-- proof
  simp [replayTopLevelMergePlan?]

end CPythonListsort

namespace CPythonListsort

/--
[topLevelFormedLengths_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma topLevelFormedLengths_empty
  {κ : Type u}
  {ν : Type v}
  {base : Nat} :
-- imply
  topLevelFormedLengths { base := base, len := 0 } [] = [] := by
-- proof
  simp [topLevelFormedLengths]

end CPythonListsort

namespace CPythonListsort

/--
[topLevelFormedLengths_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma topLevelFormedLengths_singleton
  {κ : Type u}
  {ν : Type v}
  {base : Nat} :
-- imply
  topLevelFormedLengths { base := base, len := 1 } [] = [1] := by
-- proof
  simp [topLevelFormedLengths]

end CPythonListsort

namespace CPythonListsort

/--
[replayTopLevelMergePlan_empty_cost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma replayTopLevelMergePlan_empty_cost
  {κ : Type u}
  {ν : Type v}
  {base : Nat} :
-- imply
  ∃ plan, replayTopLevelMergePlan? { base := base, len := 0 } [] = some plan ∧ plan.mergeCost = 0 :=
-- proof
⟨.empty, replayTopLevelMergePlan_empty base, rfl⟩

end CPythonListsort

namespace CPythonListsort

/--
[replayTopLevelMergePlan_singleton_cost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma replayTopLevelMergePlan_singleton_cost
  {κ : Type u}
  {ν : Type v}
  {base : Nat} :
-- imply
  ∃ plan, replayTopLevelMergePlan? { base := base, len := 1 } [] = some plan ∧ plan.runLengths = [1] ∧ plan.mergeCost = 0 :=
-- proof
⟨.tree (.leaf 1), replayTopLevelMergePlan_singleton base, rfl, rfl⟩

end CPythonListsort

namespace CPythonListsort

/--
[replayTopLevelMergePlan_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma replayTopLevelMergePlan_exact
  {κ : Type u}
  {ν : Type v}
  {input : RunSpan}
  {events : List PolicyEvent}
  {plan : MergePlan}
-- given
  (hreplay : replayTopLevelMergePlan? input events = some plan) :
-- imply
  plan.runLengths = topLevelFormedLengths input events ∧ plan.mergeCost = PolicyEvent.logicalMergeCost events := by
-- proof
  by_cases hzero : input.len = 0
  · rw [replayTopLevelMergePlan?, if_pos hzero] at hreplay
    rw [topLevelFormedLengths, if_pos hzero]
    by_cases hevents : events = []
    · subst events
      simp only [if_true, Option.some.injEq] at hreplay
      subst plan
      exact ⟨rfl, rfl⟩
    · rw [if_neg hevents] at hreplay
      contradiction
  · rw [replayTopLevelMergePlan?, if_neg hzero] at hreplay
    rw [topLevelFormedLengths, if_neg hzero]
    by_cases hone : input.len = 1
    · rw [if_pos hone] at hreplay ⊢
      by_cases hevents : events = []
      · subst events
        simp only [if_true, Option.some.injEq] at hreplay
        subst plan
        exact ⟨rfl, rfl⟩
      · rw [if_neg hevents] at hreplay
        contradiction
    · rw [if_neg hone] at hreplay ⊢
      exact replayMergePlan_exact hreplay

end CPythonListsort

namespace CPythonListsort

/--
[policyForestMatches_empty_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma policyForestMatches_empty_iff
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  PolicyForestMatches [] state ↔ state.pending.toList = [] := by
-- proof
  simp [PolicyForestMatches]

end CPythonListsort

namespace CPythonListsort

/--
[PolicyForestMatches.length_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma PolicyForestMatches.length_eq
  {κ : Type u}
  {ν : Type v}
  {forest : List SpannedMergeTree}
  {state : MergeState κ ν}
-- given
  (h : PolicyForestMatches forest state) :
-- imply
  forest.length = state.pending.size := by
-- proof
  have := congrArg List.length h
  simpa [PolicyForestMatches] using this

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[get?](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma PolicyForestMatches.get?
  {forest : List SpannedMergeTree} {state : MergeState κ ν}
  (hmatch : PolicyForestMatches forest state) {i : Nat}
  {run : PendingRun} (hrun : state.pending[i]? = some run) :
  ∃ tree, forest[i]? = some tree ∧
    tree.span = RunSpan.ofPendingRun run := by
  have hrunList : state.pending.toList[i]? = some run := by
    simpa using hrun
  have hbound : i < forest.length := by
    rw [hmatch.length_eq]
    exact (Array.getElem?_eq_some_iff.mp hrun).1
  let tree := forest[i]
  have htree : forest[i]? = some tree := by
    exact List.getElem?_eq_getElem hbound
  refine ⟨tree, htree, ?_⟩
  have hforestMapped :
    (forest.map SpannedMergeTree.span)[i]? = some tree.span := by
    simpa [List.getElem?_map] using
      congrArg (Option.map SpannedMergeTree.span) htree
  have hpendingMapped :
    (state.pending.toList.map RunSpan.ofPendingRun)[i]? =
      some (RunSpan.ofPendingRun run) := by
    simpa [List.getElem?_map] using
      congrArg (Option.map RunSpan.ofPendingRun) hrunList
  rw [hmatch, hpendingMapped] at hforestMapped
  exact (Option.some.inj hforestMapped).symm

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[runSpan_ofPendingRun_setPower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma runSpan_ofPendingRun_setPower
  (run : PendingRun) (power : Option Nat) :
  RunSpan.ofPendingRun { run with power := power } =
    RunSpan.ofPendingRun run :=
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[PolicyForestMatches.of_pending_spans_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma PolicyForestMatches.of_pending_spans_eq
  {κ : Type u}
  {ν : Type v}
  {forest : List SpannedMergeTree}
  {before after : MergeState κ ν}
-- given
  (hmatch : PolicyForestMatches forest before)
  (hspans : before.pending.toList.map RunSpan.ofPendingRun = after.pending.toList.map RunSpan.ofPendingRun) :
-- imply
  PolicyForestMatches forest after := by
-- proof
  rwa [PolicyForestMatches, ← hspans]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[getLast_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma PendingRunsCover.getLast_end
  {cursor limit : Nat} {runs : List PendingRun} {last : PendingRun}
  (hcover : PendingRunsCover cursor limit runs)
  (hlast : runs.getLast? = some last) :
  last.endIndex = limit := by
  induction runs generalizing cursor with
  | nil => simp at hlast
  | cons run rest ih =>
    obtain ⟨_hbase, _hnonnegative, _hpositive, _hwithin, := hcover
      hrest⟩
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst last
      simpa [PendingRunsCover] using hrest
    | cons next tail =>
      exact ih hrest (by simpa using hlast)

end CPythonListsort

namespace CPythonListsort

/--
[nextForestBase_eq_of_pendingLayout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma nextForestBase_eq_of_pendingLayout
  {κ : Type u}
  {ν : Type v}
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {state : MergeState κ ν}
  {scanned : Nat}
-- given
  (hinputBase : input.base = state.basekeys)
  (hmatch : PolicyForestMatches forest state)
  (hlayout : PendingLayout state scanned) :
-- imply
  nextForestBase input forest = state.basekeys + scanned := by
-- proof
  obtain hempty | := List.eq_nil_or_concat' state.pending.toList
    ⟨before, last, hsplit⟩
  · have hforestEmpty : forest = [] := by
    have hmapped : forest.map SpannedMergeTree.span = [] := by
      simpa [PolicyForestMatches, hempty] using hmatch
    simpa using hmapped
    have hcover := hlayout.2.2.2
    rw [hempty] at hcover
    simp only [PendingRunsCover] at hcover
    rw [nextForestBase, hforestEmpty]
    simp only [List.getLast?_nil]
    rw [hinputBase]
    omega
  · have hlastRun : state.pending.toList.getLast? = some last := by
    rw [hsplit]
    simp
    have hlastEnd : last.endIndex = state.basekeys + scanned :=
      hlayout.2.2.2.getLast_end hlastRun
    have hlastMapped :
      (state.pending.toList.map RunSpan.ofPendingRun).getLast? =
        some (RunSpan.ofPendingRun last) := by
      rw [List.getLast?_map, hlastRun]
      rfl
    have hforestMapped :
      (forest.map SpannedMergeTree.span).getLast? =
        some (RunSpan.ofPendingRun last) := by
      rwa [hmatch]
    rw [List.getLast?_map] at hforestMapped
    cases hlastForest : forest.getLast? with
    | none => simp [hlastForest] at hforestMapped
    | some tree =>
      simp only [hlastForest, Option.map_some, Option.some.injEq]
        at hforestMapped
      rw [nextForestBase, hlastForest]
      change tree.span.endIndex = state.basekeys + scanned
      rw [hforestMapped]
      simpa [RunSpan.ofPendingRun, RunSpan.endIndex,
        PendingRun.endIndex] using hlastEnd

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[map_span_take](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma map_span_take (forest : List SpannedMergeTree) (i : Nat) :
  (forest.take i).map SpannedMergeTree.span =
    (forest.map SpannedMergeTree.span).take i := by
  simp

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[map_span_drop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma map_span_drop (forest : List SpannedMergeTree) (i : Nat) :
  (forest.drop i).map SpannedMergeTree.span =
    (forest.map SpannedMergeTree.span).drop i := by
  simp

end CPythonListsort

namespace CPythonListsort

/--
[policyForestMatches_after_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma policyForestMatches_after_merge
  {κ : Type u}
  {ν : Type v}
  {input : RunSpan}
  {forest nextForest : List SpannedMergeTree}
  {before after : MergeState κ ν}
  {i : Nat}
  {left right : PendingRun}
-- given
  (hmatch : PolicyForestMatches forest before)
  (hleft : before.pending[i]? = some left)
  (hright : before.pending[i + 1]? = some right)
  (hafter : after.pending.toList = before.pending.toList.take i ++ ({ left with len := left.len + right.len } : PendingRun) :: before.pending.toList.drop (i + 2))
  (hsum : (left.len + right.len).toNat = left.len.toNat + right.len.toNat)
  (hreplay : applyPolicyEvent? input forest (.merge { index := i left := RunSpan.ofPendingRun left right := RunSpan.ofPendingRun right }) = some nextForest) :
-- imply
  PolicyForestMatches nextForest after := by
-- proof
  rw [applyPolicyEvent_merge_eq_some_iff] at hreplay
  rcases hreplay with
    ⟨leftTree, rightTree, hleftTree, hrightTree, hleftSpan,
      hrightSpan, _hadjacent, rfl⟩
  rw [PolicyForestMatches, hafter]
  simp only [List.map_append, List.map_cons]
  rw [map_span_take, map_span_drop, hmatch]
  have hleftPending : before.pending.toList[i]? = some left := by
    simpa using hleft
  have hrightPending : before.pending.toList[i + 1]? = some right := by
    simpa using hright
  have hleftMapped :
    (before.pending.toList.map RunSpan.ofPendingRun)[i]? =
      some (RunSpan.ofPendingRun left) := by
    simpa [List.getElem?_map] using congrArg (Option.map RunSpan.ofPendingRun) hleftPending
  have hrightMapped :
    (before.pending.toList.map RunSpan.ofPendingRun)[i + 1]? =
      some (RunSpan.ofPendingRun right) := by
    simpa [List.getElem?_map] using congrArg (Option.map RunSpan.ofPendingRun) hrightPending
  have hleftTreeSpan : leftTree.span = RunSpan.ofPendingRun left := by
    have : (forest.map SpannedMergeTree.span)[i]? = some leftTree.span := by
      simpa [List.getElem?_map] using
        congrArg (Option.map SpannedMergeTree.span) hleftTree
    rw [hmatch, hleftMapped] at this
    exact (Option.some.inj this).symm
  have hrightTreeSpan : rightTree.span = RunSpan.ofPendingRun right := by
    have : (forest.map SpannedMergeTree.span)[i + 1]? =
      some rightTree.span := by
      simpa [List.getElem?_map] using
        congrArg (Option.map SpannedMergeTree.span) hrightTree
    rw [hmatch, hrightMapped] at this
    exact (Option.some.inj this).symm
  simp [SpannedMergeTree.merge, RunSpan.merge, RunSpan.ofPendingRun,
    hleftTreeSpan, hrightTreeSpan, hsum]

end CPythonListsort

namespace CPythonListsort

/--
[mergeAt_policyReplay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma mergeAt_policyReplay
  {κ : Type u}
  {ν : Type v}
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {pre : MergeState κ ν}
  {scanned i : Nat}
  {result : MergeAtResult κ ν}
-- given
  (hmatch : PolicyForestMatches forest pre)
  (hlayout : PendingLayout pre scanned)
  (hsafety : MergeAtSafetyPost pre scanned i (mergeAtTraced? pre i) result) :
-- imply
  ∃ nextForest, replayPolicyEventsFrom? input forest (mergeAtTraced? pre i).trace.policyEvents = some nextForest ∧ PolicyForestMatches nextForest result.state := by
-- proof
  rcases hsafety.logicalMerge with
    ⟨left, right, hleft, hright, hpending, hevents⟩
  obtain ⟨leftTree, hleftTree, hleftSpan⟩ := hmatch.get? hleft
  obtain ⟨rightTree, hrightTree, hrightSpan⟩ := hmatch.get? hright
  rcases Array.exists_pair_split_of_getElem?_eq_some hleft hright with
    ⟨before, after, hbeforeLength, hsplit⟩
  have hgeometry := hlayout.adjacentPair_geometry hleft hright
  have hadjacent :
    (RunSpan.ofPendingRun left).Adjacent
      (RunSpan.ofPendingRun right) := by
    simpa [RunSpan.Adjacent, RunSpan.endIndex, RunSpan.ofPendingRun,
      PendingRun.endIndex] using hgeometry.adjacent
  let event : LogicalMergeEvent :=
    { index := i
      left := RunSpan.ofPendingRun left
      right := RunSpan.ofPendingRun right }
  let nextForest : List SpannedMergeTree :=
    forest.take i ++
      SpannedMergeTree.merge
        (replayBoundaryPower input event.left event.right)
        leftTree rightTree :: forest.drop (i + 2)
  have happly : applyPolicyEvent? input forest (.merge event) =
    some nextForest := by
    rw [applyPolicyEvent_merge_eq_some_iff]
    exact ⟨leftTree, rightTree, hleftTree, hrightTree, hleftSpan,
      hrightSpan, hadjacent, rfl⟩
  have hfit : left.len.toNat + right.len.toNat < 2 ^ 63 :=
    hlayout.pairFits hsplit
  have hfit64 : left.len.toNat + right.len.toNat < 2 ^ 64 := by
    norm_num at hfit ⊢
    omega
  have hsum : (left.len + right.len).toNat =
    left.len.toNat + right.len.toNat :=
    BitVec.toNat_add_of_lt hfit64
  have hsplice := Array.toList_set_eraseIdx_adjacent
    (xs := pre.pending) (i := i) (left := left) (right := right)
    (replacement := ({ left with len := left.len + right.len } : PendingRun))
    hsplit hbeforeLength
  have hpendingList : result.state.pending.toList =
    before ++
      ({ left with len := left.len + right.len } : PendingRun) :: after := by
    exact (congrArg Array.toList hpending).trans hsplice
  have htake : pre.pending.toList.take i = before := by
    rw [hsplit, ← hbeforeLength]
    simp
  have hdrop : pre.pending.toList.drop (i + 2) = after := by
    rw [hsplit, ← hbeforeLength]
    simp
  have hpendingTakeDrop : result.state.pending.toList =
    pre.pending.toList.take i ++
      ({ left with len := left.len + right.len } : PendingRun) ::
      pre.pending.toList.drop (i + 2) := by
    rwa [htake, hdrop]
  refine ⟨nextForest, ?_, ?_⟩
  · rw [hevents]
    change replayPolicyEventsFrom? input forest [.merge event] =
      some nextForest
    simp [replayPolicyEventsFrom?, happly]
  · exact policyForestMatches_after_merge input forest nextForest pre
    result.state i left right hmatch hleft hright hpendingTakeDrop hsum
    happly

end CPythonListsort

namespace CPythonListsort

/--
[setTopPowerTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma setTopPowerTraced_policyEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {power : Nat} :
-- imply
  (setTopPowerTraced? state power).trace.policyEvents = [] := by
-- proof
  unfold setTopPowerTraced?
  split <;>
    simp [TraceResult.failure, TraceResult.trace_pendingRunPowerWrite,
      AccessTrace.singletonAccess, AccessTrace.empty]

end CPythonListsort

namespace CPythonListsort

/--
[setTopPowerTraced_pendingSpans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma setTopPowerTraced_pendingSpans
  {κ : Type u}
  {ν : Type v}
  {state after : MergeState κ ν}
  {power : Nat}
-- given
  (hresult : (setTopPowerTraced? state power).result = some after) :
-- imply
  after.pending.toList.map RunSpan.ofPendingRun = state.pending.toList.map RunSpan.ofPendingRun := by
-- proof
  unfold setTopPowerTraced? at hresult
  split at hresult
  · simp [TraceResult.failure] at hresult
  · rename_i hnonempty
    change
      (TraceResult.pendingRunPowerWrite? state
        (Int.ofNat (state.pending.size - 1)) power).erase = some after at hresult
    rw [TraceResult.erase_pendingRunPowerWrite] at hresult
    have hnonnegative : 0 ≤ Int.ofNat (state.pending.size - 1) :=
      Int.natCast_nonneg _
    rw [if_pos hnonnegative] at hresult
    change
      (state.pending[state.pending.size - 1]?.map fun top =>
        { state with
          pending := state.pending.setIfInBounds (state.pending.size - 1)
            ({ top with power := some power } : PendingRun) }) =
        some after at hresult
    generalize hlookup : state.pending[state.pending.size - 1]? = lookup
      at hresult
    cases lookup with
    | none => simp at hresult
    | some top =>
      simp only [Option.map_some, Option.some.injEq] at hresult
      subst after
      obtain hempty | := List.eq_nil_or_concat' state.pending.toList
        ⟨before, last, hsplit⟩
      · have hsizeZero : state.pending.size = 0 := by
        simpa using congrArg List.length hempty
        rw [Array.isEmpty_iff_size_eq_zero] at hnonempty
        exact (hnonempty hsizeZero).elim
      · have hsize : state.pending.size = before.length + 1 := by
        have := congrArg List.length hsplit
        simpa using this
        have hlastLookup :
          state.pending[state.pending.size - 1]? = some last := by
          rw [← Array.getElem?_toList, hsplit, hsize]
          simp
        rw [hlookup] at hlastLookup
        have hlast : last = top :=
          (Option.some.inj hlastLookup).symm
        subst last
        rw [Array.toList_setIfInBounds, hsplit, hsize]
        simp [RunSpan.ofPendingRun]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[forall₂_split_last_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma forall₂_split_last_left
  {R : α → β → Prop} {before : List α} {last : α} {ys : List β}
  (h : List.Forall₂ R (before ++ [last]) ys) :
  ∃ pre entry,
    ys = pre ++ [entry] ∧ List.Forall₂ R before pre ∧ R last entry := by
  induction before generalizing ys with
  | nil =>
    cases h with
    | cons hentry htail =>
      cases htail
      exact ⟨[], _, rfl, .nil, hentry⟩
  | cons head before ih =>
    cases h with
    | cons hhead htail =>
      obtain ⟨pre, entry, rfl, hpre, hentry⟩ := ih htail
      exact ⟨_ :: pre, entry, by simp, .cons hhead hpre, hentry⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[forall₂_split_last_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma forall₂_split_last_right
  {R : α → β → Prop} {xs : List α} {before : List β} {last : β}
  (h : List.Forall₂ R xs (before ++ [last])) :
  ∃ pre entry,
    xs = pre ++ [entry] ∧ List.Forall₂ R pre before ∧ R entry last := by
  induction before generalizing xs with
  | nil =>
    cases h with
    | cons hentry htail =>
      cases htail
      exact ⟨[], _, rfl, .nil, hentry⟩
  | cons head before ih =>
    cases h with
    | cons hhead htail =>
      obtain ⟨pre, entry, rfl, hpre, hentry⟩ := ih htail
      exact ⟨_ :: pre, entry, by simp, .cons hhead hpre, hentry⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[forall₂_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma forall₂_append
  {R : α → β → Prop} {left₁ right₁ : List α} {left₂ right₂ : List β}
  (hleft : List.Forall₂ R left₁ left₂)
  (hright : List.Forall₂ R right₁ right₂) :
  List.Forall₂ R (left₁ ++ right₁) (left₂ ++ right₂) := by
  induction hleft with
  | nil => simpa using hright
  | cons hhead htail ih => exact .cons hhead ih

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[newestRootLeaf_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma newestRootLeaf_split
  {forest : List SpannedMergeTree}
  (h : NewestRootLeaf forest) (hne : forest ≠ []) :
  ∃ before span,
    forest = before ++ [SpannedMergeTree.leaf span] := by
  induction h with
  | empty => contradiction
  | singleton span => exact ⟨[], span, rfl⟩
  | prepend entry right rest htail ih =>
    obtain ⟨before, span, hsplit⟩ := ih (by simp)
    exact ⟨entry :: before, span, by simp [hsplit]⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[newestRootLeaf_append_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma newestRootLeaf_append_leaf
  (forest : List SpannedMergeTree) (span : RunSpan) :
  NewestRootLeaf (forest ++ [SpannedMergeTree.leaf span]) := by
  induction forest with
  | nil => exact .singleton span
  | cons entry rest ih =>
    cases rest with
    | nil => exact .prepend entry (SpannedMergeTree.leaf span) [] (.singleton span)
    | cons right tail =>
      exact .prepend entry right (tail ++ [SpannedMergeTree.leaf span]) ih

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[scanPowerForestInv_to_found](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma scanPowerForestInv_to_found
  {input : RunSpan} {forest : List SpannedMergeTree}
  {state : MergeState κ ν} {power : Nat} {newRun : PendingRun}
  (h : ScanPowerForestInv input forest state)
  (hnonempty : state.pending.toList ≠ [])
  (hpower : ∀ before top,
    state.pending.toList = before ++ [top] →
      power = pendingBoundaryPower state.basekeys state.listlen top newRun) :
  FoundPowerForestInv input power newRun forest state := by
  have hforestNonempty : forest ≠ [] := by
    intro hforest
    have hlength := h.aligned.length_eq
    apply hnonempty
    apply List.eq_nil_of_length_eq_zero
    simpa [hforest] using hlength.symm
  rcases newestRootLeaf_split h.newestRootLeaf hforestNonempty with
    ⟨beforeForest, span, hforest⟩
  have haligned : List.Forall₂ (RunTreeAligned input)
    (beforeForest ++ [SpannedMergeTree.leaf span]) state.pending.toList := by
    simpa only [← hforest] using h.aligned
  rcases forall₂_split_last_left haligned with
    ⟨beforeRuns, topRun, hpending, hbefore, htop⟩
  refine ⟨h.inputMax, h.basekeys_eq, h.listlen_eq, beforeForest,
    SpannedMergeTree.leaf span, beforeRuns, topRun, hforest, hpending,
    hpower beforeRuns topRun hpending, hbefore, htop.span_eq, htop.valid,
    htop.powerValid, ?_, ?_⟩
  · simp [SpannedMergeTree.leaf, MergeTree.rootPower]
  · simp [SpannedMergeTree.leaf, MergeTree.rootPower]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[setTopPowerTraced_pending_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma setTopPowerTraced_pending_frame
  (state after : MergeState κ ν) (power : Nat)
  (before : List PendingRun) (top : PendingRun)
  (hsplit : state.pending.toList = before ++ [top])
  (hresult : (setTopPowerTraced? state power).result = some after) :
  after.pending.toList =
    before ++ [{ top with power := some power }] ∧
    after.listlen = state.listlen ∧ after.basekeys = state.basekeys := by
  unfold setTopPowerTraced? at hresult
  have hnonempty : state.pending.isEmpty ≠ true := by
    intro hempty
    rw [Array.isEmpty_iff] at hempty
    rw [hempty] at hsplit
    simp at hsplit
  rw [if_neg hnonempty] at hresult
  change
    (TraceResult.pendingRunPowerWrite? state
      (Int.ofNat (state.pending.size - 1)) power).erase = some after at hresult
  rw [TraceResult.erase_pendingRunPowerWrite] at hresult
  have hnonnegative : (0 : Int) ≤ Int.ofNat (state.pending.size - 1) := by
    simpa only [Int.ofNat_eq_natCast] using
      (Int.natCast_nonneg (state.pending.size - 1))
  rw [if_pos hnonnegative] at hresult
  change
    (state.pending[state.pending.size - 1]?.map fun top =>
      { state with
        pending := state.pending.setIfInBounds (state.pending.size - 1)
          ({ top with power := some power } : PendingRun) }) = some after
      at hresult
  have hsize : state.pending.size = before.length + 1 := by
    have := congrArg List.length hsplit
    simpa using this
  have hlookup : state.pending[state.pending.size - 1]? = some top := by
    rw [← Array.getElem?_toList, hsplit, hsize]
    simp
  rw [hlookup] at hresult
  injection hresult with hafter
  subst after
  refine ⟨?_, rfl, rfl⟩
  rw [Array.toList_setIfInBounds, hsplit, hsize]
  simp

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[newRun_not_mem_of_pendingLayout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma newRun_not_mem_of_pendingLayout
  {state : MergeState κ ν} {scanned : Nat} {newRun : PendingRun}
  (hlayout : PendingLayout state scanned)
  (hnewBase : newRun.base = state.basekeys + scanned) :
  newRun ∉ state.pending.toList := by
  intro hmem
  have hspec := hlayout.2.2.2.member_spec hmem
  simp only [PendingRun.endIndex] at hspec
  rw [hnewBase] at hspec
  omega

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[foundPowerForestInv_finish](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma foundPowerForestInv_finish
  {input : RunSpan} {power : Nat} {forest : List SpannedMergeTree}
  {state after : MergeState κ ν} {newRun : PendingRun}
  (hghost : FoundPowerForestInv input power newRun forest state)
  (hset : (setTopPowerTraced? state power).result = some after)
  (hnewBase : input.base ≤ newRun.base)
  (hnewEnd : newRun.base + newRun.len.toNat ≤ input.base + input.len)
  (hnewPositive : 0 < newRun.len.toNat) :
  ScanPowerForestInv input
    (forest ++ [SpannedMergeTree.leaf (RunSpan.ofPendingRun newRun)])
    (pushPendingRun after newRun) := by
  rcases hghost with
    ⟨hinputMax, hbasekeys, hlistlen, beforeForest, topTree, beforeRuns, topRun,
      hforest, hpending, _hpower,
      hbeforeAligned, htopSpan, htopValid, htopPowerValid,
      hprospectiveBelow, _holderBelow⟩
  rcases setTopPowerTraced_pending_frame state after power beforeRuns topRun
    hpending hset with ⟨hafterPending, hafterListlen, hafterBasekeys⟩
  let poweredTop : PendingRun := { topRun with power := some power }
  have htopAligned : RunTreeAligned input topTree poweredTop := by
    refine
      { span_eq := by
        simpa [poweredTop, RunSpan.ofPendingRun] using htopSpan
        valid := htopValid
        powerValid := htopPowerValid
        outgoingBelowRoot := ?_ }
    intro boundaryPower rootPower hboundary hroot
    have hboundaryEq : boundaryPower = power := by
      simpa [poweredTop] using Option.some.inj hboundary.symm
    subst boundaryPower
    exact hprospectiveBelow rootPower hroot
  have hleafAligned : RunTreeAligned input
    (SpannedMergeTree.leaf (RunSpan.ofPendingRun newRun)) newRun := by
    refine
      { span_eq := rfl
        valid := SpannedMergeTree.leaf_valid _
        powerValid := ?_
        outgoingBelowRoot := ?_ }
    · simp only [SpannedMergeTree.leaf, MergeTree.PowerValid,
      RunSpan.ofPendingRun]
      rw [listSizeWord_toNat hinputMax]
      exact ⟨hnewBase, hnewEnd, hnewPositive⟩
    · simp [SpannedMergeTree.leaf, MergeTree.rootPower]
  refine
    { inputMax := hinputMax
      basekeys_eq := ?_
      listlen_eq := ?_
      aligned := ?_
      newestRootLeaf := newestRootLeaf_append_leaf forest
        (RunSpan.ofPendingRun newRun) }
  · simpa [pushPendingRun] using hafterBasekeys.trans hbasekeys
  · simpa [pushPendingRun] using hafterListlen.trans hlistlen
  · rw [hforest]
    simp only [pushPendingRun, Array.toList_push, hafterPending,
      List.append_assoc]
    exact forall₂_append hbeforeAligned
      (.cons htopAligned (.cons hleafAligned .nil))

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergedTree_powerValid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma mergedTree_powerValid
  (input : RunSpan) (left right : SpannedMergeTree)
  (hinputMax : input.len ≤ PY_LIST_MAX)
  (hleftValid : left.Valid) (hrightValid : right.Valid)
  (hleftPowerValid : left.tree.PowerValid input.base
    (BitVec.ofNat 64 input.len) left.span.base)
  (hrightPowerValid : right.tree.PowerValid input.base
    (BitVec.ofNat 64 input.len) right.span.base)
  (hleftWithin : left.span.ValidWithin input)
  (hrightWithin : right.span.ValidWithin input)
  (hadjacent : left.span.Adjacent right.span)
  (hleftHeap : ∀ childPower,
    left.tree.rootPower = some childPower →
      replayBoundaryPower input left.span right.span < childPower)
  (hrightHeap : ∀ childPower,
    right.tree.rootPower = some childPower →
      replayBoundaryPower input left.span right.span < childPower) :
  let merged := SpannedMergeTree.merge
    (replayBoundaryPower input left.span right.span) left right
  merged.Valid ∧
    merged.tree.PowerValid input.base (BitVec.ofNat 64 input.len)
      merged.span.base := by
  dsimp only
  have hleftLength : left.tree.totalLength = left.span.len := hleftValid
  have hrightLength : right.tree.totalLength = right.span.len := hrightValid
  refine ⟨SpannedMergeTree.merge_valid _ hleftValid hrightValid, ?_⟩
  simp only [SpannedMergeTree.merge, MergeTree.PowerValid]
  refine ⟨hleftWithin.1, ?_, hleftPowerValid, ?_, ?_, ?_,
    hleftHeap, hrightHeap⟩
  · have hrightEnd := hrightWithin.2.1
    rw [hleftLength, hrightLength, listSizeWord_toNat hinputMax]
    simp only [RunSpan.merge]
    simp only [RunSpan.Adjacent, RunSpan.endIndex] at hadjacent
    simp only [RunSpan.endIndex] at hrightEnd
    omega
  · have hrightBase :
    left.span.base + left.tree.totalLength = right.span.base := by
    have hadjacent' := hadjacent
    simp only [RunSpan.Adjacent, RunSpan.endIndex] at hadjacent'
    rwa [hleftLength]
    simpa [SpannedMergeTree.merge, RunSpan.merge, hrightBase] using
      hrightPowerValid
  · simpa [SpannedMergeTree.merge, RunSpan.merge, hleftLength,
    hrightLength] using
    (replayBoundaryPower_valid_input input left.span right.span
      hinputMax hleftWithin hrightWithin hadjacent)
  · simp [replayBoundaryPower, SpannedMergeTree.merge, RunSpan.merge,
    hleftLength, hrightLength]

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[pendingRunRead_result_of_get?](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma pendingRunRead_result_of_get?
  (state : MergeState κ ν) (i : Nat) (run : PendingRun)
  (hget : state.pending[i]? = some run) :
  (TraceResult.pendingRunRead? state (Int.ofNat i)).result = some run := by
  change (TraceResult.pendingRunRead? state (Int.ofNat i)).erase = some run
  rw [TraceResult.erase_pendingRunRead]
  have hnonnegative : 0 ≤ Int.ofNat i := Int.natCast_nonneg _
  rw [if_pos hnonnegative]
  simpa using hget

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[traceResult_bind_result_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma traceResult_bind_result_of_eq_some
  (current : TraceResult α) (next : α → TraceResult β) (value : α)
  (hresult : current.result = some value) :
  (current.bind next).result = (next value).result := by
  change (current.bind next).erase = (next value).erase
  rw [TraceResult.erase_bind]
  change current.result.bind (fun item => (next item).result) = _
  rw [hresult]
  rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[traceResult_map_result_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma traceResult_map_result_of_eq_some
  (current : TraceResult α) (transform : α → β) (value : α)
  (hresult : current.result = some value) :
  (current.map transform).result = some (transform value) := by
  change (current.map transform).erase = some (transform value)
  rw [TraceResult.erase_map]
  change current.result.map transform = _
  rw [hresult]
  rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[foundNewRunLoop_policyReplay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
`foundNewRunLoopTraced?` contributes an accepted merge-only replay segment.
The terminal top-power write changes no represented span. -/
private lemma foundNewRunLoop_policyReplay
  (input : RunSpan) (forest : List SpannedMergeTree)
  (fuel : Nat) (state : MergeState κ ν) (scanned power : Nat)
  (newRun : PendingRun) (result : FoundNewRunResult κ ν)
  (hmatch : PolicyForestMatches forest state)
  (hresult :
    (foundNewRunLoopTraced? fuel state power).result = some result)
  (hcode : result.returnCode = 0)
  (hresultFuel : result.fuelExhausted = false)
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hlayout : PendingLayout state scanned)
  (hpowered : PoweredPrefix state)
  (hghost : FoundPowerForestInv input power newRun forest state)
  (hnewBase : newRun.base = state.basekeys + scanned)
  (hnewNonnegative : newRun.len.Nonnegative)
  (hnewPositive : 0 < newRun.len.toNat)
  (hnewWithin : scanned + newRun.len.toNat ≤ state.listlen.toNat)
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
  ∃ nextForest,
    replayPolicyEventsFrom? input forest
      (foundNewRunLoopTraced? fuel state power).trace.policyEvents =
      some nextForest ∧
    PolicyForestMatches nextForest result.state ∧
    ScanPowerForestInv input
      (nextForest ++ [SpannedMergeTree.leaf (RunSpan.ofPendingRun newRun)])
      (pushPendingRun result.state newRun) := by
  induction fuel generalizing state forest result with
  | zero =>
    simp only [foundNewRunLoopTraced?] at hresult
    injection hresult with hresultEq
    subst result
    change true = false at hresultFuel
    contradiction
  | succ remaining ih =>
    by_cases hmany : 1 < state.pending.size
    · let i := state.pending.size - 2
      have hi : i < state.pending.size := by
        dsimp [i]
        omega
      let preceding := state.pending[i]
      have hget : state.pending[i]? = some preceding :=
        Array.getElem?_eq_getElem hi
      have hread :
        (TraceResult.pendingRunRead? state (Int.ofNat i)).result =
          some preceding :=
        pendingRunRead_result_of_get? state i preceding hget
      have hresult' := hresult
      simp only [foundNewRunLoopTraced?, hmany, if_true] at hresult'
      rw [traceResult_bind_result_of_eq_some _ _ preceding hread] at hresult'
      cases hstored : preceding.power with
      | none =>
        simp only [hstored] at hresult'
        change none = some result at hresult'
        contradiction
      | some precedingPower =>
        simp only [hstored] at hresult'
        by_cases hguard : power < precedingPower
        · rw [if_pos hguard] at hresult'
          have hposition : i + 2 = state.pending.size ∨
            i + 3 = state.pending.size := by
            left
            dsimp [i]
            omega
          rcases mergeAt_safe state scanned i hlayout hmax hposition
            hInv hLive hMode with ⟨merged, hmerged⟩
          rw [traceResult_bind_result_of_eq_some _ _ merged
            hmerged.resultEq] at hresult'
          have hsuccess :
            merged.returnCode = 0 ∧ !merged.fuelExhausted :=
            ⟨hmerged.returnCode, by simp [hmerged.resultFuel]⟩
          rw [if_pos hsuccess] at hresult'
          rcases mergeAt_policyReplay input forest state scanned i merged
            hmatch hlayout hmerged with
            ⟨middle, hmergeReplay, hmiddleMatch⟩
          rcases hghost with
            ⟨hinputMax, hinputBase, hinputLength, beforeForest, topTree,
              beforeRuns, topRun, hforestEq, hpendingEq,
              hprospectiveExact, hbeforeAligned, htopSpan, htopValid,
              htopPowerValid, hprospectiveBelow, holderBelow⟩
          obtain hbeforeEmpty | := List.eq_nil_or_concat' beforeRuns
            ⟨olderRuns, leftRun, hbeforeRuns⟩
          · subst beforeRuns
            have hsize := congrArg List.length hpendingEq
            simp at hsize
            omega
          have hbeforeAligned' : List.Forall₂ (RunTreeAligned input)
            beforeForest (olderRuns ++ [leftRun]) := by
            simpa [hbeforeRuns] using hbeforeAligned
          rcases forall₂_split_last_right hbeforeAligned' with
            ⟨olderForest, leftTree, hbeforeForest, holderAligned,
              hleftAligned⟩
          have hstateSplit : state.pending.toList =
            olderRuns ++ [leftRun, topRun] := by
            rw [hpendingEq, hbeforeRuns]
            simp [List.append_assoc]
          have hforestSplit : forest =
            olderForest ++ [leftTree, topTree] := by
            rw [hforestEq, hbeforeForest]
            simp [List.append_assoc]
          have hsize : state.pending.size = olderRuns.length + 2 := by
            have := congrArg List.length hstateSplit
            simpa using this
          have hiEq : i = olderRuns.length := by
            dsimp [i]
            omega
          have hleftGet : state.pending[i]? = some leftRun := by
            rw [← Array.getElem?_toList, hstateSplit, hiEq]
            simp
          have hprecedingEq : preceding = leftRun := by
            rw [hget] at hleftGet
            exact Option.some.inj hleftGet
          have hstoredLeft : leftRun.power = some precedingPower := by
            rwa [← hprecedingEq]
          have hleftPowerExact : leftRun.power = some
            (pendingBoundaryPower state.basekeys state.listlen
              leftRun topRun) := by
            apply hpowered.boundary_power (before := olderRuns)
              (after := [])
            simpa [List.append_assoc] using hstateSplit
          have hprecedingPowerExact : precedingPower =
            pendingBoundaryPower state.basekeys state.listlen
              leftRun topRun := by
            rw [hstoredLeft] at hleftPowerExact
            exact Option.some.inj hleftPowerExact
          have hmergeRaw : mergeAt? state i = some merged := by
            rwa [← hmerged.exactErasure]
          have hpolicy := mergeTop_preserves_poweredPrefix state scanned
            olderRuns leftRun topRun newRun precedingPower power merged
            hmax hlayout hpowered
            hstateSplit
            hnewBase hnewNonnegative hnewPositive hnewWithin
            (newRun_not_mem_of_pendingLayout hlayout hnewBase) hstoredLeft
            hprecedingPowerExact hprospectiveExact hguard
            (by simpa [i, hiEq] using hmergeRaw) hmerged.returnCode
            hmerged.resultFuel
          let mergedRun : PendingRun :=
            { leftRun with len := leftRun.len + topRun.len }
          have hmergedPending : merged.state.pending.toList =
            olderRuns ++ [mergedRun] := by
            simpa [mergedRun] using hpolicy.1
          have hmergedPowered : PoweredPrefix merged.state :=
            hpolicy.2.2.2.1
          have hmergedProspective : power = pendingBoundaryPower
            merged.state.basekeys merged.state.listlen mergedRun newRun := by
            simpa [mergedRun] using hpolicy.2.2.2.2
          have hword : state.listlen.toNat = input.len := by
            rw [hinputLength, listSizeWord_toNat hinputMax]
          have hcover : PendingRunsCover state.basekeys
            (state.basekeys + scanned)
            (olderRuns ++ [leftRun, topRun]) := by
            simpa [hstateSplit] using hlayout.2.2.2
          have hleftSpec := hcover.member_spec
            (run := leftRun) (by simp)
          have htopSpec := hcover.member_spec
            (run := topRun) (by simp)
          have hpair := hcover.pair_spec (before := olderRuns)
            (after := []) (left := leftRun) (right := topRun)
          have hleftWithin : leftTree.span.ValidWithin input := by
            rw [hleftAligned.span_eq]
            refine ⟨?_, ?_, ?_⟩
            · simpa [RunSpan.ofPendingRun, hinputBase] using hleftSpec.1
            · simp only [RunSpan.ofPendingRun, RunSpan.endIndex]
              rwa [← hinputBase, ← hword]
                (Nat.add_le_add_left hlayout.2.2.1 state.basekeys)
            · simpa [RunSpan.ofPendingRun] using hleftSpec.2.2.1
          have htopWithin : topTree.span.ValidWithin input := by
            rw [htopSpan]
            refine ⟨?_, ?_, ?_⟩
            · simpa [RunSpan.ofPendingRun, hinputBase] using htopSpec.1
            · simp only [RunSpan.ofPendingRun, RunSpan.endIndex]
              rwa [← hinputBase, ← hword]
                (Nat.add_le_add_left hlayout.2.2.1 state.basekeys)
            · simpa [RunSpan.ofPendingRun] using htopSpec.2.2.1
          have hadjacent : leftTree.span.Adjacent topTree.span := by
            rw [hleftAligned.span_eq, htopSpan]
            simpa [RunSpan.Adjacent, RunSpan.endIndex,
              RunSpan.ofPendingRun, PendingRun.endIndex] using
                hpair.2.2.2.2
          have hnodePower : replayBoundaryPower input leftTree.span
            topTree.span = precedingPower := by
            calc
              replayBoundaryPower input leftTree.span topTree.span =
                pendingBoundaryPower state.basekeys state.listlen
                  leftRun topRun := by
                simp [replayBoundaryPower, pendingBoundaryPower,
                  hinputBase, hinputLength, hleftAligned.span_eq,
                  htopSpan, RunSpan.ofPendingRun]
              _ = precedingPower := hprecedingPowerExact.symm
          have htreeFacts := mergedTree_powerValid input leftTree topTree
            hinputMax hleftAligned.valid htopValid hleftAligned.powerValid
            htopPowerValid hleftWithin htopWithin hadjacent
            (fun childPower hroot => by
              rw [hnodePower]
              exact hleftAligned.outgoingBelowRoot precedingPower
                childPower hstoredLeft hroot)
            (fun childPower hroot => by
              rw [hnodePower]
              exact holderBelow leftRun (by simp [hbeforeRuns])
                precedingPower childPower hstoredLeft hroot)
          let mergedTree : SpannedMergeTree :=
            SpannedMergeTree.merge precedingPower leftTree topTree
          have hmergedTreeValid : mergedTree.Valid := by
            simpa [mergedTree, hnodePower] using htreeFacts.1
          have hmergedTreePowerValid : mergedTree.tree.PowerValid
            input.base (BitVec.ofNat 64 input.len)
              mergedTree.span.base := by
            simpa [mergedTree, hnodePower] using htreeFacts.2
          rcases hmerged.logicalMerge with
            ⟨actualLeft, actualRight, hactualLeft, hactualRight,
              _hpending, hmergeEvents⟩
          have hrightGet : state.pending[i + 1]? = some topRun := by
            rw [← Array.getElem?_toList, hstateSplit, hiEq]
            simp
          have hactualLeftEq : actualLeft = leftRun := by
            rw [hleftGet] at hactualLeft
            exact Option.some.inj hactualLeft.symm
          have hactualRightEq : actualRight = topRun := by
            rw [hrightGet] at hactualRight
            exact Option.some.inj hactualRight.symm
          subst actualLeft
          subst actualRight
          let event : LogicalMergeEvent :=
            { index := i
              left := RunSpan.ofPendingRun leftRun
              right := RunSpan.ofPendingRun topRun }
          have holderLength : olderForest.length = olderRuns.length :=
            holderAligned.length_eq
          have hiForest : i = olderForest.length :=
            hiEq.trans holderLength.symm
          have hnodePowerRuns : replayBoundaryPower input
            (RunSpan.ofPendingRun leftRun)
              (RunSpan.ofPendingRun topRun) = precedingPower := by
            simpa [hleftAligned.span_eq, htopSpan] using hnodePower
          have happlyMiddle : applyPolicyEvent? input forest
            (.merge event) = some middle := by
            have hreplay := hmergeReplay
            rw [hmergeEvents] at hreplay
            simpa [event, replayPolicyEventsFrom?] using hreplay
          have hleftTreeGet : forest[i]? = some leftTree := by
            rw [hforestSplit, hiForest]
            simp
          have htopTreeGet : forest[i + 1]? = some topTree := by
            rw [hforestSplit, hiForest]
            simp
          have happlyExpected : applyPolicyEvent? input forest
            (.merge event) = some (olderForest ++ [mergedTree]) := by
            rw [applyPolicyEvent_merge_eq_some_iff]
            refine ⟨leftTree, topTree, hleftTreeGet, htopTreeGet,
              hleftAligned.span_eq, htopSpan, ?_, ?_⟩
            · change (RunSpan.ofPendingRun leftRun).Adjacent
              (RunSpan.ofPendingRun topRun)
              simpa [RunSpan.Adjacent, RunSpan.endIndex,
                RunSpan.ofPendingRun, PendingRun.endIndex] using
                hpair.2.2.2.2
            · simp [event, hforestSplit, hiForest, mergedTree,
              hnodePowerRuns]
          have hmiddleEq : middle = olderForest ++ [mergedTree] := by
            rw [happlyExpected] at happlyMiddle
            exact Option.some.inj happlyMiddle.symm
          have hfit : leftRun.len.toNat + topRun.len.toNat < 2 ^ 63 :=
            hlayout.pairFits (by
              simpa [List.append_assoc] using hstateSplit)
          have hfit64 : leftRun.len.toNat + topRun.len.toNat < 2 ^ 64 := by
            norm_num at hfit ⊢
            omega
          have hsum : (leftRun.len + topRun.len).toNat =
            leftRun.len.toNat + topRun.len.toNat :=
            BitVec.toNat_add_of_lt hfit64
          have hmergedSpan : mergedTree.span =
            RunSpan.ofPendingRun mergedRun := by
            simp [mergedTree, mergedRun, SpannedMergeTree.merge,
              RunSpan.merge, RunSpan.ofPendingRun,
              hleftAligned.span_eq, htopSpan, hsum]
          have hincreasingWithLeft : IncreasingPendingPowers
            (olderRuns ++ [leftRun]) := by
            apply hpowered.increasing_of_eq_snoc
            simpa [List.append_assoc] using hstateSplit
          have hmergedGhost : FoundPowerForestInv input power newRun
            middle merged.state := by
            refine ⟨hinputMax, ?_, ?_, olderForest, mergedTree,
              olderRuns, mergedRun, hmiddleEq, hmergedPending,
              hmergedProspective, holderAligned, hmergedSpan,
              hmergedTreeValid, hmergedTreePowerValid, ?_, ?_⟩
            · exact hmerged.stableFrame.basekeys.trans hinputBase
            · exact hmerged.stableFrame.listlen.trans hinputLength
            · intro rootPower hroot
              simp [mergedTree, SpannedMergeTree.merge,
                MergeTree.rootPower] at hroot
              subst rootPower
              exact hguard
            · intro run hrun storedPower rootPower hrunPower hroot
              have hrootEq : rootPower = precedingPower := by
                simpa [mergedTree, SpannedMergeTree.merge,
                  MergeTree.rootPower] using Option.some.inj hroot.symm
              subst rootPower
              exact hincreasingWithLeft.power_lt_last hrun hrunPower
                hstoredLeft
          have hmergedMax : merged.state.listlen.toNat ≤ PY_LIST_MAX := by
            rwa [hmerged.stableFrame.listlen]
          rcases ih middle merged.state result
            hmiddleMatch hresult' hcode hresultFuel hmergedMax
            hmerged.pendingLayout hmergedPowered hmergedGhost
            (by rw [hmerged.stableFrame.basekeys]; exact hnewBase)
            (by rw [hmerged.stableFrame.listlen]; exact hnewWithin)
            hmerged.tempInvariant hmerged.tempLive
            hmerged.valuesMode with
            ⟨nextForest, hrest, hnextMatch, hnextPower⟩
          refine ⟨nextForest, ?_, hnextMatch, hnextPower⟩
          have hevents :
            (foundNewRunLoopTraced? (remaining + 1) state
              power).trace.policyEvents =
              (mergeAtTraced? state i).trace.policyEvents ++
                (foundNewRunLoopTraced? remaining merged.state
                  power).trace.policyEvents := by
            have hread' :
              (TraceResult.pendingRunRead? state
                (Int.ofNat (state.pending.size - 2))).result =
                  some preceding := by
              simpa [i] using hread
            rw [foundNewRunLoopTraced?, if_pos hmany,
              TraceResult.policyEvents_bind, hread']
            simp only [TraceResult.trace_pendingRunRead,
              AccessTrace.singletonAccess, hstored, hguard, if_true,
              List.nil_append]
            have hmergeResult :
              (mergeAtTraced? state
                (state.pending.size - 2)).result = some merged := by
              simpa [i] using hmerged.resultEq
            rw [TraceResult.policyEvents_bind, hmergeResult]
            simp only
            rw [if_pos hsuccess]
          rwa [hevents, replayPolicyEventsFrom_append, hmergeReplay]
        · rw [if_neg hguard] at hresult'
          cases hset : (setTopPowerTraced? state power).result with
          | none =>
            change
              (setTopPowerTraced? state power).result.map _ =
                some result at hresult'
            rw [hset] at hresult'
            contradiction
          | some after =>
            change
              (setTopPowerTraced? state power).result.map _ =
                some result at hresult'
            rw [hset] at hresult'
            injection hresult' with hresultEq
            subst result
            refine ⟨forest, ?_, ?_, ?_⟩
            · have hevents :
              (foundNewRunLoopTraced? (remaining + 1) state
                power).trace.policyEvents = [] := by
              have hread' :
                (TraceResult.pendingRunRead? state
                  (Int.ofNat (state.pending.size - 2))).result =
                    some preceding := by
                simpa [i] using hread
              rw [foundNewRunLoopTraced?, if_pos hmany,
                TraceResult.policyEvents_bind, hread']
              simp only [TraceResult.trace_pendingRunRead,
                AccessTrace.singletonAccess, List.nil_append,
                hstored, hguard, if_false,
                TraceResult.policyEvents_map]
              exact setTopPowerTraced_policyEvents_eq_nil state power
              rw [hevents]
              rfl
            · apply hmatch.of_pending_spans_eq
              exact (setTopPowerTraced_pendingSpans state after power
                hset).symm
            · apply foundPowerForestInv_finish hghost hset
              · rw [hnewBase, hghost.2.1]
                exact Nat.le_add_right _ _
              · rw [hnewBase, hghost.2.1]
                have hword : state.listlen.toNat = input.len := by
                  rw [hghost.2.2.1, listSizeWord_toNat hghost.1]
                rw [hword] at hnewWithin
                omega
              · exact hnewPositive
    · have hresult' := hresult
      simp only [foundNewRunLoopTraced?, hmany, if_false] at hresult'
      cases hset : (setTopPowerTraced? state power).result with
      | none =>
        change
          (setTopPowerTraced? state power).result.map _ =
            some result at hresult'
        rw [hset] at hresult'
        contradiction
      | some after =>
        change
          (setTopPowerTraced? state power).result.map _ =
            some result at hresult'
        rw [hset] at hresult'
        injection hresult' with hresultEq
        subst result
        refine ⟨forest, ?_, ?_, ?_⟩
        · have hevents :
          (foundNewRunLoopTraced? (remaining + 1) state
            power).trace.policyEvents = [] := by
          simp only [foundNewRunLoopTraced?, hmany, if_false,
            TraceResult.policyEvents_map,
            setTopPowerTraced_policyEvents_eq_nil]
          rw [hevents]
          rfl
        · apply hmatch.of_pending_spans_eq
          exact (setTopPowerTraced_pendingSpans state after power hset).symm
        · apply foundPowerForestInv_finish hghost hset
          · rw [hnewBase, hghost.2.1]
            exact Nat.le_add_right _ _
          · rw [hnewBase, hghost.2.1]
            have hword : state.listlen.toNat = input.len := by
              rw [hghost.2.2.1, listSizeWord_toNat hghost.1]
            rw [hword] at hnewWithin
            omega
          · exact hnewPositive

end CPythonListsort

namespace CPythonListsort

/--
[foundNewRun_policyReplay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma foundNewRun_policyReplay
  {κ : Type u}
  {ν : Type v}
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {state : MergeState κ ν}
  {scanned : Nat}
  {newRun : PendingRun}
  {result : FoundNewRunResult κ ν}
-- given
  (hmatch : PolicyForestMatches forest state)
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hlayout : PendingLayout state scanned)
  (hpowered : PoweredPrefix state)
  (hpowerInv : ScanPowerForestInv input forest state)
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
  (hsafety : FoundNewRunSafetyPost state scanned newRun result) :
-- imply
  ∃ nextForest, replayPolicyEventsFrom? input forest (foundNewRunTraced? state newRun.len.toNat).trace.policyEvents = some nextForest ∧ PolicyForestMatches nextForest result.state ∧ ScanPowerForestInv input (nextForest ++ [SpannedMergeTree.leaf (RunSpan.ofPendingRun newRun)]) (pushPendingRun result.state newRun) := by
-- proof
  by_cases hempty : state.pending.isEmpty = true
  · have hresult := hsafety.resultEq
    rw [foundNewRunTraced?, if_pos hempty] at hresult
    injection hresult with hresultEq
    have hresultState : result.state = state :=
      (congrArg FoundNewRunResult.state hresultEq).symm
    have hpendingEmpty : state.pending.toList = [] := by
      simpa [Array.isEmpty_iff] using hempty
    have hforestEmpty : forest = [] := by
      have hlength := hpowerInv.aligned.length_eq
      rw [hpendingEmpty] at hlength
      exact List.eq_nil_of_length_eq_zero (by simpa using hlength)
    subst forest
    refine ⟨[], ?_, ?_, ?_⟩
    · simp [foundNewRunTraced?, hempty, TraceResult.pure,
      AccessTrace.empty, replayPolicyEventsFrom?]
    · rw [hresultState]
      simpa [PolicyForestMatches, hpendingEmpty]
    · have hnewBaseInput : input.base ≤ newRun.base := by
      rw [hsafety.readyToPush.new_run_adjacent, hresultState,
        hpowerInv.basekeys_eq]
      exact Nat.le_add_right _ _
      have hword : state.listlen.toNat = input.len := by
        rw [hpowerInv.listlen_eq, listSizeWord_toNat hpowerInv.inputMax]
      have hnewEnd : newRun.base + newRun.len.toNat ≤
        input.base + input.len := by
        rw [hsafety.readyToPush.new_run_adjacent, hresultState,
          hpowerInv.basekeys_eq, ← hword]
        have hwithin := hsafety.readyToPush.new_run_within_input
        rw [hsafety.stableFrame.listlen] at hwithin
        omega
      have hleaf : RunTreeAligned input
        (SpannedMergeTree.leaf (RunSpan.ofPendingRun newRun)) newRun := by
        refine
          { span_eq := rfl
            valid := SpannedMergeTree.leaf_valid _
            powerValid := ?_
            outgoingBelowRoot := ?_ }
        · simp only [SpannedMergeTree.leaf, MergeTree.PowerValid,
          RunSpan.ofPendingRun]
          rw [listSizeWord_toNat hpowerInv.inputMax]
          exact ⟨hnewBaseInput, hnewEnd,
            hsafety.readyToPush.new_run_nonempty.2⟩
        · simp [SpannedMergeTree.leaf, MergeTree.rootPower]
      refine
        { inputMax := hpowerInv.inputMax
          basekeys_eq := by
            rw [hresultState]
            simpa [pushPendingRun] using hpowerInv.basekeys_eq
          listlen_eq := by
            rw [hresultState]
            simpa [pushPendingRun] using hpowerInv.listlen_eq
          aligned := ?_
          newestRootLeaf := .singleton (RunSpan.ofPendingRun newRun) }
      rw [hresultState]
      simpa [pushPendingRun, hpendingEmpty] using
        (List.Forall₂.cons hleaf List.Forall₂.nil)
  · have hsizePositive : 0 < state.pending.size := by
    rw [Array.isEmpty_iff_size_eq_zero] at hempty
    omega
    let top := state.pending[state.pending.size - 1]
    have htopGet : state.pending[state.pending.size - 1]? = some top :=
      Array.getElem?_eq_getElem (by omega)
    have htopRead :
      (TraceResult.pendingRunRead? state
        (Int.ofNat (state.pending.size - 1))).result = some top :=
      pendingRunRead_result_of_get? state _ top htopGet
    have hresult := hsafety.resultEq
    rw [foundNewRunTraced?, if_neg hempty] at hresult
    rw [traceResult_bind_result_of_eq_some _ _ top htopRead] at hresult
    by_cases hguard :
      ((!state.listlen.msb) && decide (state.basekeys ≤ top.base) &&
        (0 : PySSize).slt top.len && decide (0 < newRun.len.toNat) &&
        decide (newRun.len.toNat ≤ PY_SSIZE_T_MAX) &&
        decide (top.base - state.basekeys + top.len.toNat +
          newRun.len.toNat ≤ state.listlen.toNat)) = true
    · rw [if_pos hguard] at hresult
      let powered := powerloopTraced
        (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
        (BitVec.ofNat 64 newRun.len.toNat) state.listlen
      change
        (if !powered.stopped then _ else
          foundNewRunLoopTraced? state.pending.size state
            powered.result).result = some result at hresult
      by_cases hnotStopped : (!powered.stopped) = true
      · rw [if_pos hnotStopped] at hresult
        injection hresult with hresultEq
        subst result
        have hfuel := hsafety.resultFuel
        change true = false at hfuel
        contradiction
      · rw [if_neg hnotStopped] at hresult
        obtain hnil | := List.eq_nil_or_concat' state.pending.toList
          ⟨before, last, hstateSplit⟩
        · have hzero : state.pending.size = 0 := by
          simpa using congrArg List.length hnil
          omega
        have hlastGet : state.pending[state.pending.size - 1]? = some last := by
          have hsize : state.pending.size = before.length + 1 := by
            have := congrArg List.length hstateSplit
            simpa using this
          rw [← Array.getElem?_toList, hstateSplit, hsize]
          simp
        rw [htopGet] at hlastGet
        have hlastEq : last = top := Option.some.inj hlastGet.symm
        subst last
        have hnewLen : BitVec.ofNat 64 newRun.len.toNat = newRun.len := by simp
        have hpower : powered.result = pendingBoundaryPower state.basekeys
          state.listlen top newRun := by
          dsimp [powered, pendingBoundaryPower, powerloop]
          rw [hnewLen]
        have hghost : FoundPowerForestInv input powered.result newRun forest
          state := by
          apply scanPowerForestInv_to_found hpowerInv
          · simpa [hstateSplit]
          · intro actualBefore actualTop hactualSplit
            have hsplits : actualBefore ++ [actualTop] = before ++ [top] :=
              hactualSplit.symm.trans hstateSplit
            have hlast := congrArg List.getLast? hsplits
            have hsome : some actualTop = some top := by simpa using hlast
            have htopEq : actualTop = top := Option.some.inj hsome
            subst actualTop
            exact hpower
        have hnewBaseInitial : newRun.base = state.basekeys + scanned := by
          rwa [← hsafety.stableFrame.basekeys]
        have hnewWithinInitial : scanned + newRun.len.toNat ≤
          state.listlen.toNat := by
          rwa [← hsafety.stableFrame.listlen]
        rcases foundNewRunLoop_policyReplay input forest state.pending.size
          state scanned powered.result newRun result hmatch hresult
          hsafety.returnCode hsafety.resultFuel hmax hlayout hpowered hghost
          hnewBaseInitial
          hsafety.readyToPush.new_run_nonempty.1
          hsafety.readyToPush.new_run_nonempty.2
          hnewWithinInitial hInv hLive hMode
          with ⟨nextForest, hreplay, hnextMatch, hnextPower⟩
        refine ⟨nextForest, ?_, hnextMatch, hnextPower⟩
        have hevents :
          (foundNewRunTraced? state newRun.len.toNat).trace.policyEvents =
            (foundNewRunLoopTraced? state.pending.size state
              powered.result).trace.policyEvents := by
          rw [foundNewRunTraced?, if_neg hempty,
            TraceResult.policyEvents_bind, htopRead]
          simp only [TraceResult.trace_pendingRunRead,
            AccessTrace.singletonAccess, List.nil_append]
          rw [if_pos hguard]
          change
            (if !powered.stopped then _ else
              foundNewRunLoopTraced? state.pending.size state
                powered.result).trace.policyEvents =
              (foundNewRunLoopTraced? state.pending.size state
                powered.result).trace.policyEvents
          rw [if_neg hnotStopped]
        rwa [hevents]
    · rw [if_neg hguard] at hresult
      contradiction

end CPythonListsort

namespace CPythonListsort

/--
[pushFormedRun_policyReplay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma pushFormedRun_policyReplay
  {κ : Type u}
  {ν : Type v}
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {state : MergeState κ ν}
  {scanned remaining : Nat}
  {newRun : PendingRun}
  {naturalLength target : Nat}
-- given
  (hinputBase : input.base = state.basekeys)
  (hinputLength : input.len = state.listlen.toNat)
  (hmatch : PolicyForestMatches forest state)
  (hlayout : PendingLayout state scanned)
  (hnewBase : newRun.base = state.basekeys + scanned)
  (hpartition : scanned + remaining = state.listlen.toNat)
  (hpositive : 0 < newRun.len.toNat)
  (hwithin : newRun.len.toNat ≤ remaining)
  (hlengthRelation : FormedLengthRelation { run := RunSpan.ofPendingRun newRun depthAfter := state.pending.size + 1 naturalLength := naturalLength target := target remainingBefore := remaining }) :
-- imply
  let push : PendingPushEvent := { run := RunSpan.ofPendingRun newRun depthAfter := state.pending.size + 1 naturalLength := naturalLength target := target remainingBefore := remaining } replayPolicyEventsFrom? input forest [.formed push] = some (forest ++ [SpannedMergeTree.leaf push.run]) ∧ PolicyForestMatches (forest ++ [SpannedMergeTree.leaf push.run]) (pushPendingRun state newRun) := by
-- proof
  dsimp only
  let push : PendingPushEvent :=
    { run := RunSpan.ofPendingRun newRun
      depthAfter := state.pending.size + 1
      naturalLength := naturalLength
      target := target
      remainingBefore := remaining }
  let nextForest := forest ++ [SpannedMergeTree.leaf push.run]
  have hvalid : ValidFormedEvent input forest push := by
    refine ⟨?_, ?_, ?_, ?_, ?_, hlengthRelation⟩
    · simpa [push] using hmatch.length_eq.symm
    · rw [nextForestBase_eq_of_pendingLayout input forest state scanned
      hinputBase hmatch hlayout]
      simpa [push, RunSpan.ofPendingRun] using hnewBase
    · simp only [push, RunSpan.ofPendingRun, RunSpan.endIndex]
      rw [hnewBase, hinputBase, hinputLength]
      omega
    · simpa [push, RunSpan.ofPendingRun] using hpositive
    · simpa [push, RunSpan.ofPendingRun] using hwithin
  have happly : applyPolicyEvent? input forest (.formed push) =
    some nextForest := by
    rw [applyPolicyEvent_formed_eq_some_iff]
    exact ⟨hvalid, rfl⟩
  refine ⟨?_, ?_⟩
  · change
    (applyPolicyEvent? input forest
      (.formed
        { run := RunSpan.ofPendingRun newRun
          depthAfter := state.pending.size + 1
          naturalLength := naturalLength
          target := target
          remainingBefore := remaining })).bind
        (fun middle => replayPolicyEventsFrom? input middle []) =
      some nextForest
    rw [show applyPolicyEvent? input forest
      (.formed
        { run := RunSpan.ofPendingRun newRun
          depthAfter := state.pending.size + 1
          naturalLength := naturalLength
          target := target
          remainingBefore := remaining }) = some nextForest by
      simpa [push] using happly]
    rfl
  · simp only [PolicyForestMatches, pushPendingRun,
    Array.toList_push, List.map_append, List.map_singleton,
    SpannedMergeTree.leaf]
    rw [hmatch]

end CPythonListsort

namespace CPythonListsort

/--
[forceCollapseIndexTraced_policyEvents_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma forceCollapseIndexTraced_policyEvents_eq_nil
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  (forceCollapseIndexTraced? state).trace.policyEvents = [] := by
-- proof
  unfold forceCollapseIndexTraced?
  by_cases hmany : 1 < state.pending.size
  · rw [if_pos hmany]
    dsimp only
    by_cases hpositive : 0 < state.pending.size - 2
    · rw [if_pos hpositive]
      apply TraceResult.policyEvents_bind_eq_nil
      · simp [TraceResult.trace_pendingRunRead,
        AccessTrace.singletonAccess]
      · intro previous
        simp [TraceResult.policyEvents_map,
          TraceResult.trace_pendingRunRead, AccessTrace.singletonAccess]
    · rw [if_neg hpositive]
      rfl
  · rw [if_neg hmany]
    rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeForceCollapseLoop_policyReplay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
segment from its incoming open forest to the returned singleton forest. -/
private lemma mergeForceCollapseLoop_policyReplay
  (input : RunSpan) (forest : List SpannedMergeTree)
  (fuel : Nat) (state : MergeState κ ν) (scanned : Nat)
  (result : MergeForceCollapseResult κ ν)
  (hmatch : PolicyForestMatches forest state)
  (hresult :
    (mergeForceCollapseLoopTraced? fuel state).result = some result)
  (hcode : result.returnCode = 0)
  (hresultFuel : result.fuelExhausted = false)
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hlayout : PendingLayout state scanned)
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
  ∃ nextForest,
    replayPolicyEventsFrom? input forest
      (mergeForceCollapseLoopTraced? fuel state).trace.policyEvents =
      some nextForest ∧
    PolicyForestMatches nextForest result.state := by
  induction fuel generalizing state forest result with
  | zero =>
    by_cases hdone : state.pending.size ≤ 1
    · have hresult' := hresult
      rw [mergeForceCollapseLoopTraced?, if_pos hdone] at hresult'
      injection hresult' with hresultEq
      subst result
      refine ⟨forest, ?_, hmatch⟩
      rw [mergeForceCollapseLoopTraced?, if_pos hdone]
      change replayPolicyEventsFrom? input forest [] = some forest
      rfl
    · have hresult' := hresult
      rw [mergeForceCollapseLoopTraced?, if_neg hdone] at hresult'
      injection hresult' with hresultEq
      subst result
      have hfuel := hresultFuel
      change true = false at hfuel
      contradiction
  | succ remaining ih =>
    by_cases hmany : 1 < state.pending.size
    · rcases forceCollapseIndexTraced_safe state hmany with
      ⟨i, hindex, _hindexSafe, _hindexErase, hposition⟩
      rcases mergeAt_safe state scanned i hlayout hmax hposition
        hInv hLive hMode with ⟨merged, hmerged⟩
      have hsuccess : merged.returnCode = 0 ∧ !merged.fuelExhausted :=
        ⟨hmerged.returnCode, by simp [hmerged.resultFuel]⟩
      have hresult' := hresult
      rw [mergeForceCollapseLoopTraced?, if_pos hmany,
        traceResult_bind_result_of_eq_some _ _ i hindex,
        traceResult_bind_result_of_eq_some _ _ merged hmerged.resultEq,
        if_pos hsuccess] at hresult'
      rcases mergeAt_policyReplay input forest state scanned i merged
        hmatch hlayout hmerged with
        ⟨middle, hmergeReplay, hmiddleMatch⟩
      have hmergedMax : merged.state.listlen.toNat ≤ PY_LIST_MAX := by
        rwa [hmerged.stableFrame.listlen]
      rcases ih middle merged.state result hmiddleMatch hresult' hcode
        hresultFuel hmergedMax hmerged.pendingLayout hmerged.tempInvariant
        hmerged.tempLive hmerged.valuesMode with
        ⟨nextForest, hrest, hnextMatch⟩
      refine ⟨nextForest, ?_, hnextMatch⟩
      have hevents :
        (mergeForceCollapseLoopTraced? (remaining + 1)
          state).trace.policyEvents =
          (mergeAtTraced? state i).trace.policyEvents ++
            (mergeForceCollapseLoopTraced? remaining
              merged.state).trace.policyEvents := by
        rw [mergeForceCollapseLoopTraced?, if_pos hmany,
          TraceResult.policyEvents_bind, hindex]
        simp only [forceCollapseIndexTraced_policyEvents_eq_nil,
          List.nil_append]
        rw [TraceResult.policyEvents_bind, hmerged.resultEq]
        simp only
        rw [if_pos hsuccess]
      rwa [hevents, replayPolicyEventsFrom_append, hmergeReplay]
    · have hresult' := hresult
      rw [mergeForceCollapseLoopTraced?, if_neg hmany] at hresult'
      injection hresult' with hresultEq
      subst result
      refine ⟨forest, ?_, hmatch⟩
      rw [mergeForceCollapseLoopTraced?, if_neg hmany]
      change replayPolicyEventsFrom? input forest [] = some forest
      rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeForceCollapse_policyReplay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma mergeForceCollapse_policyReplay
  {κ : Type u}
  {ν : Type v}
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {state : MergeState κ ν}
  {scanned : Nat}
  {result : MergeForceCollapseResult κ ν}
-- given
  (hmatch : PolicyForestMatches forest state)
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hlayout : PendingLayout state scanned)
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
  (hsafety : MergeForceCollapseSafetyPost state scanned result) :
-- imply
  ∃ nextForest, replayPolicyEventsFrom? input forest (mergeForceCollapseTraced? state).trace.policyEvents = some nextForest ∧ PolicyForestMatches nextForest result.state := by
-- proof
  exact mergeForceCollapseLoop_policyReplay input forest state.pending.size
    state scanned result hmatch (by simpa [mergeForceCollapseTraced?] using
      hsafety.resultEq) hsafety.returnCode hsafety.resultFuel hmax hlayout hInv
      hLive hMode

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeForceCollapseLoop_formedLengths_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
events.  In particular it never fabricates a formed-run observation; all
formed events belong to the scan prefix before this call boundary. -/
private lemma mergeForceCollapseLoop_formedLengths_eq_nil
  (fuel : Nat) (state : MergeState κ ν) (scanned : Nat)
  (result : MergeForceCollapseResult κ ν)
  (hresult :
    (mergeForceCollapseLoopTraced? fuel state).result = some result)
  (hcode : result.returnCode = 0)
  (hresultFuel : result.fuelExhausted = false)
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hlayout : PendingLayout state scanned)
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data) :
  PolicyEvent.formedLengths
    (mergeForceCollapseLoopTraced? fuel state).trace.policyEvents = [] := by
  induction fuel generalizing state result with
  | zero =>
    by_cases hdone : state.pending.size ≤ 1
    · rw [mergeForceCollapseLoopTraced?, if_pos hdone]
      rfl
    · have hresult' := hresult
      rw [mergeForceCollapseLoopTraced?, if_neg hdone] at hresult'
      injection hresult' with hresultEq
      subst result
      change true = false at hresultFuel
      contradiction
  | succ remaining ih =>
    by_cases hmany : 1 < state.pending.size
    · rcases forceCollapseIndexTraced_safe state hmany with
      ⟨i, hindex, _hindexSafe, _hindexErase, hposition⟩
      rcases mergeAt_safe state scanned i hlayout hmax hposition
        hInv hLive hMode with ⟨merged, hmerged⟩
      have hsuccess : merged.returnCode = 0 ∧ !merged.fuelExhausted :=
        ⟨hmerged.returnCode, by simp [hmerged.resultFuel]⟩
      have hresult' := hresult
      rw [mergeForceCollapseLoopTraced?, if_pos hmany,
        traceResult_bind_result_of_eq_some _ _ i hindex,
        traceResult_bind_result_of_eq_some _ _ merged hmerged.resultEq,
        if_pos hsuccess] at hresult'
      have hmergedMax : merged.state.listlen.toNat ≤ PY_LIST_MAX := by
        rwa [hmerged.stableFrame.listlen]
      have htail := ih merged.state result hresult' hcode hresultFuel
        hmergedMax hmerged.pendingLayout hmerged.tempInvariant
        hmerged.tempLive hmerged.valuesMode
      have hevents :
        (mergeForceCollapseLoopTraced? (remaining + 1)
          state).trace.policyEvents =
          (mergeAtTraced? state i).trace.policyEvents ++
            (mergeForceCollapseLoopTraced? remaining
              merged.state).trace.policyEvents := by
        rw [mergeForceCollapseLoopTraced?, if_pos hmany,
          TraceResult.policyEvents_bind, hindex]
        simp only [forceCollapseIndexTraced_policyEvents_eq_nil,
          List.nil_append]
        rw [TraceResult.policyEvents_bind, hmerged.resultEq]
        simp only
        rw [if_pos hsuccess]
      rcases hmerged.logicalMerge with
        ⟨left, right, _hleft, _hright, _hpending, hmergeEvents⟩
      rw [hevents, PolicyEvent.formedLengths_append, hmergeEvents,
        htail]
      rfl
    · rw [mergeForceCollapseLoopTraced?, if_neg hmany]
      rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeForceCollapseTraced_formedLengths_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma mergeForceCollapseTraced_formedLengths_eq_nil
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {scanned : Nat}
  {result : MergeForceCollapseResult κ ν}
-- given
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hlayout : PendingLayout state scanned)
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
  (hsafety : MergeForceCollapseSafetyPost state scanned result) :
-- imply
  PolicyEvent.formedLengths (mergeForceCollapseTraced? state).trace.policyEvents = [] := by
-- proof
  unfold mergeForceCollapseTraced?
  exact mergeForceCollapseLoop_formedLengths_eq_nil state.pending.size state
    scanned result (by simpa [mergeForceCollapseTraced?] using hsafety.resultEq)
    hsafety.returnCode hsafety.resultFuel hmax hlayout hInv hLive hMode

end CPythonListsort

namespace CPythonListsort

/--
[StrongPolicyTraceReplaySplit.toReplay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma StrongPolicyTraceReplaySplit.toReplay
  {κ : Type u}
  {ν : Type v}
  {input : RunSpan}
  {initialForest : List SpannedMergeTree}
  {reverse : Bool}
  {inputSize : Nat}
  {execution : TraceResult (ListSortImplResult κ ν)}
  {post : StrongPolicyTraceReplaySplit input initialForest reverse inputSize execution} :
-- imply
  PolicyTraceReplaySplit input initialForest execution := by
-- proof
  rcases post with
    ⟨openState, openForest, closedForest, scanEvents, collapseEvents,
      collapsed, witness⟩
  exact ⟨openState, openForest, closedForest, scanEvents, collapseEvents,
    collapsed, witness.replay⟩

end CPythonListsort

namespace CPythonListsort

/--
[StrongPolicyTraceReplaySplit.of_policyEvents_eq_and_reached](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma StrongPolicyTraceReplaySplit.of_policyEvents_eq_and_reached
  {κ : Type u}
  {ν : Type v}
  {input : RunSpan}
  {initialForest : List SpannedMergeTree}
  {reverse : Bool}
  {inputSize : Nat}
  {first second : TraceResult (ListSortImplResult κ ν)}
  {post : StrongPolicyTraceReplaySplit input initialForest reverse inputSize first}
-- given
  (hevents : first.trace.policyEvents = second.trace.policyEvents)
  (hreached : ∀ (openState : MergeState κ ν) (collapsed : MergeForceCollapseResult κ ν), ListSortScanReachedCollapse reverse inputSize openState collapsed first → ListSortScanReachedCollapse reverse inputSize openState collapsed second) :
-- imply
  StrongPolicyTraceReplaySplit input initialForest reverse inputSize second := by
-- proof
  rcases post with
    ⟨openState, openForest, closedForest, scanEvents, collapseEvents,
      collapsed, witness⟩
  refine ⟨openState, openForest, closedForest, scanEvents, collapseEvents,
    collapsed, ?_⟩
  exact
    { replay :=
      { traceSplit := hevents.symm.trans witness.replay.traceSplit
        scanReplay := witness.replay.scanReplay
        openMatch := witness.replay.openMatch
        openLayout := witness.replay.openLayout
        openPowered := witness.replay.openPowered
        collapseSafety := witness.replay.collapseSafety
        collapseEvents_eq := witness.replay.collapseEvents_eq
        collapseReplay := witness.replay.collapseReplay
        closedMatch := witness.replay.closedMatch }
      openPowerInv := witness.openPowerInv
      openTempInvariant := witness.openTempInvariant
      openTempLive := witness.openTempLive
      openValuesMode := witness.openValuesMode
      collapseFormedLengths := witness.collapseFormedLengths
      reachedCollapse := hreached openState collapsed
        witness.reachedCollapse }

end CPythonListsort

namespace CPythonListsort

/--
[ListSortScanStrongWitness.collapseResultEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma ListSortScanStrongWitness.collapseResultEq
  {κ : Type u}
  {ν : Type v}
  {input : RunSpan}
  {initialForest : List SpannedMergeTree}
  {reverse : Bool}
  {inputSize : Nat}
  {execution : TraceResult (ListSortImplResult κ ν)}
  {openState : MergeState κ ν}
  {openForest closedForest : List SpannedMergeTree}
  {scanEvents collapseEvents : List PolicyEvent}
  {collapsed : MergeForceCollapseResult κ ν}
  {witness : ListSortScanStrongWitness input initialForest reverse inputSize execution openState openForest closedForest scanEvents collapseEvents collapsed} :
-- imply
  (mergeForceCollapseTraced? openState).result = some collapsed :=
-- proof
witness.reachedCollapse.collapse_result_eq

end CPythonListsort

namespace CPythonListsort

/--
[PolicyTraceReplaySplit.of_policyEvents_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma PolicyTraceReplaySplit.of_policyEvents_eq
  {κ : Type u}
  {ν : Type v}
  {input : RunSpan}
  {initialForest : List SpannedMergeTree}
  {first second : TraceResult (ListSortImplResult κ ν)}
  {post : PolicyTraceReplaySplit input initialForest first}
-- given
  (hevents : first.trace.policyEvents = second.trace.policyEvents) :
-- imply
  PolicyTraceReplaySplit input initialForest second := by
-- proof
  rcases post with
    ⟨openState, openForest, closedForest, scanEvents, collapseEvents,
      collapsed, witness⟩
  refine ⟨openState, openForest, closedForest, scanEvents, collapseEvents,
    collapsed, ?_⟩
  exact
    { traceSplit := hevents.symm.trans witness.traceSplit
      scanReplay := witness.scanReplay
      openMatch := witness.openMatch
      openLayout := witness.openLayout
      openPowered := witness.openPowered
      collapseSafety := witness.collapseSafety
      collapseEvents_eq := witness.collapseEvents_eq
      collapseReplay := witness.collapseReplay
      closedMatch := witness.closedMatch }

end CPythonListsort

namespace CPythonListsort

/--
[listSortScan_policyReplay_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma listSortScan_policyReplay_terminal
  {κ : Type u}
  {ν : Type v}
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {fuel : Nat}
  {state : MergeState κ ν}
  {lo scanned : Nat}
  {reverse : Bool}
  {inputSize : Nat}
  {lt : BoolComparator κ}
-- given
  (hasKeyfunc : Bool)
  (hinputLength : input.len = inputSize)
  (hmatch : PolicyForestMatches forest state)
  (hpowerInv : ScanPowerForestInv input forest state)
  (hInv : ListSortScanInvariant lt hasKeyfunc inputSize state lo scanned 0) :
-- imply
  ListSortScanStrongPost input forest fuel state lo 0 reverse inputSize := by
-- proof
  have hScanned : 0 < scanned := by
    have hLower := hInv.inputSizeLower
    have hPartition := hInv.partition
    omega
  have hPending : state.pending.toList ≠ [] :=
    hInv.pendingLayout.pending_nonempty hScanned
  rcases mergeForceCollapse_safe state scanned
    (by simpa [hInv.listlen] using hInv.inputSizeMax) hPending
    hInv.pendingLayout hInv.tempInvariant hInv.tempLive hInv.valuesMode with
    ⟨collapsed, hcollapsed⟩
  rcases mergeForceCollapse_policyReplay input forest state scanned collapsed
    hmatch (by simpa [hInv.listlen] using hInv.inputSizeMax)
    hInv.pendingLayout hInv.tempInvariant hInv.tempLive hInv.valuesMode
    hcollapsed with ⟨closedForest, hcollapseReplay, hclosedMatch⟩
  have hScannedAll : scanned = inputSize := by
    have := hInv.partition
    omega
  have htrace :
    (listSortScanTraced? fuel state lo 0 reverse
      inputSize).trace.policyEvents =
      (mergeForceCollapseTraced? state).trace.policyEvents := by
    cases fuel <;>
      simp only [listSortScanTraced?,
        TraceResult.policyEvents_bind, hcollapsed.resultEq,
        hcollapsed.returnCode, hcollapsed.resultFuel, Bool.not_false,
        and_self, if_true, finishListSortTraced_policyEvents_eq_nil,
        List.append_nil]
  refine ⟨state, forest, closedForest, [],
    (mergeForceCollapseTraced? state).trace.policyEvents, collapsed, ?_⟩
  exact
    { replay :=
      { traceSplit := by simpa using htrace
        scanReplay := rfl
        openMatch := hmatch
        openLayout := by simpa [hinputLength, hScannedAll] using
          hInv.pendingLayout
        openPowered := hInv.poweredPrefix
        collapseSafety := by
          simpa [hScannedAll, hinputLength] using hcollapsed
        collapseEvents_eq := rfl
        collapseReplay := hcollapseReplay
        closedMatch := hclosedMatch }
      openPowerInv := hpowerInv
      openTempInvariant := hInv.tempInvariant
      openTempLive := hInv.tempLive
      openValuesMode := hInv.valuesMode
      collapseFormedLengths :=
        mergeForceCollapseTraced_formedLengths_eq_nil state scanned collapsed
          (by simpa [hInv.listlen] using hInv.inputSizeMax)
          hInv.pendingLayout hInv.tempInvariant hInv.tempLive hInv.valuesMode
          hcollapsed
      reachedCollapse := .terminal fuel lo hcollapsed.resultEq
        hcollapsed.returnCode hcollapsed.resultFuel }

end CPythonListsort

namespace CPythonListsort

/--
[pendingLayout_of_policy_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma pendingLayout_of_policy_frame
  {κ : Type u}
  {ν : Type v}
  {before after : MergeState κ ν}
  {scanned : Nat}
-- given
  (hLayout : PendingLayout before scanned)
  (hListlen : after.listlen = before.listlen)
  (hBasekeys : after.basekeys = before.basekeys)
  (hDataSize : after.data.entries.size = before.data.entries.size)
  (hPending : after.pending.toList = before.pending.toList) :
-- imply
  PendingLayout after scanned := by
-- proof
  unfold PendingLayout at hLayout ⊢
  rwa [hListlen, hBasekeys, hDataSize, hPending]

end CPythonListsort

namespace CPythonListsort

/--
[poweredPrefix_of_policy_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma poweredPrefix_of_policy_frame
  {κ : Type u}
  {ν : Type v}
  {before after : MergeState κ ν}
-- given
  (hPowered : PoweredPrefix before)
  (hListlen : after.listlen = before.listlen)
  (hBasekeys : after.basekeys = before.basekeys)
  (hPending : after.pending.toList = before.pending.toList) :
-- imply
  PoweredPrefix after := by
-- proof
  unfold PoweredPrefix at hPowered ⊢
  rwa [hListlen, hBasekeys, hPending]

end CPythonListsort

namespace CPythonListsort

/--
[scanPowerForestInv_of_policy_frame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma scanPowerForestInv_of_policy_frame
  {κ : Type u}
  {ν : Type v}
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {before after : MergeState κ ν}
-- given
  (hPower : ScanPowerForestInv input forest before)
  (hListlen : after.listlen = before.listlen)
  (hBasekeys : after.basekeys = before.basekeys)
  (hPending : after.pending.toList = before.pending.toList) :
-- imply
  ScanPowerForestInv input forest after := by
-- proof
  exact
    { inputMax := hPower.inputMax
      basekeys_eq := hBasekeys.trans hPower.basekeys_eq
      listlen_eq := hListlen.trans hPower.listlen_eq
      aligned := by simpa [hPending] using hPower.aligned
      newestRootLeaf := hPower.newestRootLeaf }

end CPythonListsort

namespace CPythonListsort

/--
[listSortAfterExtension_policyReplay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
lemma listSortAfterExtension_policyReplay
  {κ : Type u}
  {ν : Type v}
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {next : MergeState κ ν → Nat → Nat → TraceResult (ListSortImplResult κ ν)}
  {state : MergeState κ ν}
  {lo scanned remaining runLength : Nat}
  {naturalLength target : Nat}
  {reverse : Bool}
  {inputSize : Nat}
-- given
  (hinputBase : input.base = state.basekeys)
  (hinputLength : input.len = state.listlen.toNat)
  (hmatch : PolicyForestMatches forest state)
  (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
  (hlayout : PendingLayout state scanned)
  (hpowered : PoweredPrefix state)
  (hpowerInv : ScanPowerForestInv input forest state)
  (hbase : lo = state.basekeys + scanned)
  (hpartition : scanned + remaining = state.listlen.toNat)
  (hrunPositive : 0 < runLength)
  (hrunWithin : scanned + runLength ≤ state.listlen.toNat)
  (hrunRemaining : runLength ≤ remaining)
  (hnaturalPositive : 0 < naturalLength)
  (hnaturalRemaining : naturalLength ≤ remaining)
  (htargetPositive : 0 < target)
  (hlengthBranch : (naturalLength < target ∧ runLength = min remaining target) ∨ (target ≤ naturalLength ∧ runLength = naturalLength))
  (hInv : TempStorageInv state.a state.alloced)
  (hLive : state.a.Live)
  (hMode : SortSlice.ValuesModeInvariant state.a.hasValues state.data)
  (hContinuation : ∀ (found : FoundNewRunResult κ ν) (middleForest : List SpannedMergeTree), let newRun : PendingRun := { base := lo, len := BitVec.ofNat 64 runLength, power := none } FoundNewRunSafetyPost state scanned newRun found → PolicyForestMatches middleForest found.state → ScanPowerForestInv input (middleForest ++ [SpannedMergeTree.leaf (RunSpan.ofPendingRun newRun)]) (pushPendingRun found.state newRun) → StrongPolicyTraceReplaySplit input (middleForest ++ [SpannedMergeTree.leaf (RunSpan.ofPendingRun newRun)]) reverse inputSize (next (pushPendingRun found.state newRun) (lo + runLength) (remaining - runLength))) :
-- imply
  StrongPolicyTraceReplaySplit input forest reverse inputSize (listSortAfterExtensionTraced? next lo remaining reverse inputSize naturalLength target (state, runLength, false)) := by
-- proof
  let newRun : PendingRun :=
    { base := lo, len := BitVec.ofNat 64 runLength, power := none }
  have hRunMax : runLength ≤ PY_LIST_MAX := by omega
  have hRunNat : newRun.len.toNat = runLength := by
    simpa [newRun] using listSizeWord_toNat hRunMax
  have hRunNonnegative : newRun.len.Nonnegative := by
    simpa [newRun] using listSizeWord_nonnegative hRunMax
  have hNewBase : newRun.base = state.basekeys + scanned := by
    simpa [newRun] using hbase
  rcases foundNewRun_safe state scanned newRun hmax hlayout hpowered hNewBase
    hRunNonnegative (by simpa [hRunNat] using hrunPositive)
    (by simpa [hRunNat] using hrunWithin) hInv hLive hMode with
    ⟨found, hfound⟩
  rcases foundNewRun_policyReplay input forest state scanned newRun found
    hmatch hmax hlayout hpowered hpowerInv hInv hLive hMode hfound with
    ⟨middleForest, hfoundReplay, hmiddleMatch, hpushedPower⟩
  have hFoundBase : input.base = found.state.basekeys := by
    rwa [hfound.stableFrame.basekeys]
  have hFoundLength : input.len = found.state.listlen.toNat := by
    rwa [hfound.stableFrame.listlen]
  have hFoundPartition : scanned + remaining = found.state.listlen.toNat := by
    rwa [hfound.stableFrame.listlen]
  have hLengthRelation : FormedLengthRelation
    { run := RunSpan.ofPendingRun newRun
      depthAfter := found.state.pending.size + 1
      naturalLength := naturalLength
      target := target
      remainingBefore := remaining } := by
    refine ⟨hnaturalPositive, hnaturalRemaining, htargetPositive, ?_⟩
    obtain hshort | hlong := hlengthBranch
    · exact Or.inl ⟨hshort.1, by simpa [RunSpan.ofPendingRun,
      hRunNat] using hshort.2⟩
    · exact Or.inr ⟨hlong.1, by simpa [RunSpan.ofPendingRun,
      hRunNat] using hlong.2⟩
  rcases pushFormedRun_policyReplay input middleForest found.state scanned
    remaining newRun naturalLength target hFoundBase hFoundLength
    hmiddleMatch hfound.readyToPush.layout
    hfound.readyToPush.new_run_adjacent hFoundPartition
    (by simpa [hRunNat] using hrunPositive)
    (by simpa [hRunNat] using hrunRemaining) hLengthRelation with
    ⟨hpushReplay, hpushedMatch⟩
  rcases hContinuation found middleForest hfound hmiddleMatch hpushedPower with
    ⟨openState, openForest, closedForest, scanEvents, collapseEvents,
      collapsed, continuation⟩
  let foundEvents :=
    (foundNewRunTraced? state runLength).trace.policyEvents
  let pushEvent : PolicyEvent := .formed
    { run := RunSpan.ofPendingRun newRun
      depthAfter := found.state.pending.size + 1
      naturalLength := naturalLength
      target := target
      remainingBefore := remaining }
  refine ⟨openState, openForest, closedForest,
    foundEvents ++ pushEvent :: scanEvents, collapseEvents, collapsed, ?_⟩
  refine
    { replay :=
      { traceSplit := ?_
        scanReplay := ?_
        openMatch := continuation.replay.openMatch
        openLayout := continuation.replay.openLayout
        openPowered := continuation.replay.openPowered
        collapseSafety := continuation.replay.collapseSafety
        collapseEvents_eq := continuation.replay.collapseEvents_eq
        collapseReplay := continuation.replay.collapseReplay
        closedMatch := continuation.replay.closedMatch }
      openPowerInv := continuation.openPowerInv
      openTempInvariant := continuation.openTempInvariant
      openTempLive := continuation.openTempLive
      openValuesMode := continuation.openValuesMode
      collapseFormedLengths := continuation.collapseFormedLengths
      reachedCollapse := ?_ }
  · have hValid : ¬(runLength = 0 ∨ remaining < runLength) := by omega
    have hFoundEq :
      (foundNewRunTraced? state runLength).result = some found := by
      simpa [hRunNat] using hfound.resultEq
    have hSuccess : found.returnCode = 0 ∧ !found.fuelExhausted :=
      ⟨hfound.returnCode, by simp [hfound.resultFuel]⟩
    have hevents := listSortAfterExtensionTraced_policyEvents_of_success
      next state lo remaining runLength reverse inputSize naturalLength target
      found hValid hFoundEq hSuccess
    dsimp only at hevents
    rw [hevents, continuation.replay.traceSplit]
    simp only [foundEvents, pushEvent, newRun]
    simp [List.append_assoc]
  · rw [replayPolicyEventsFrom_append]
    have hfoundReplay' : replayPolicyEventsFrom? input forest foundEvents =
      some middleForest := by
      simpa [foundEvents, hRunNat] using hfoundReplay
    rw [hfoundReplay']
    change replayPolicyEventsFrom? input middleForest
      (pushEvent :: scanEvents) = some openForest
    change replayPolicyEventsFrom? input middleForest
      ([pushEvent] ++ scanEvents) = some openForest
    rw [replayPolicyEventsFrom_append]
    have hpushReplay' : replayPolicyEventsFrom? input middleForest
      [pushEvent] =
        some (middleForest ++
          [SpannedMergeTree.leaf (RunSpan.ofPendingRun newRun)]) := by
      simpa [pushEvent] using hpushReplay
    rwa [hpushReplay']
  · have hValid : ¬(runLength = 0 ∨ remaining < runLength) := by omega
    have hFoundEq :
      (foundNewRunTraced? state runLength).result = some found := by
      simpa [hRunNat] using hfound.resultEq
    have hSuccess : found.returnCode = 0 ∧ !found.fuelExhausted :=
      ⟨hfound.returnCode, by simp [hfound.resultFuel]⟩
    have hPushEq :
      (pushFormedRunTraced found.state newRun naturalLength target
        remaining).result = some (pushPendingRun found.state newRun) := by
      exact erase_pushFormedRunTraced _ _ _ _ _
    have hPushReached := ListSortScanReachedCollapse.through_bind
      (pushFormedRunTraced found.state newRun naturalLength target remaining)
      (fun nextState => next nextState (lo + runLength)
        (remaining - runLength))
      (pushPendingRun found.state newRun) hPushEq
      continuation.reachedCollapse
    have hFoundReached := ListSortScanReachedCollapse.through_bind
      (foundNewRunTraced? state runLength)
      (fun nextFound =>
        if nextFound.returnCode = 0 ∧ !nextFound.fuelExhausted then
          let nextRun : PendingRun :=
            { base := lo
              len := BitVec.ofNat 64 runLength
              power := none }
          (pushFormedRunTraced nextFound.state nextRun naturalLength target
            remaining).bind fun nextState =>
              next nextState (lo + runLength) (remaining - runLength)
        else
          failFromFoundNewRunTraced? nextFound reverse inputSize)
      found hFoundEq (by simpa [hSuccess, newRun] using hPushReached)
    simpa [listSortAfterExtensionTraced?, hValid] using hFoundReached

end CPythonListsort

/--
[PolicyForestMatches.get](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma get_eq
  {κ : Type u}
  {ν : Type v}
  {forest : List SpannedMergeTree}
  {state : MergeState κ ν}
  {i : Nat}
  {run : PendingRun}
-- given
  (hmatch : PolicyForestMatches forest state)
  (hrun : state.pending[i]? = some run) :
-- imply
  ∃ tree, forest[i]? = some tree ∧ tree.span = RunSpan.ofPendingRun run := by
-- proof
  apply CPythonListsort.PolicyForestMatches.get hmatch hrun

/--
[ListSortScanStrongWitness.openPowerValid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma openPowerValid_eq
  {κ : Type u}
  {ν : Type v}
  {input : RunSpan}
  {initialForest : List SpannedMergeTree}
  {reverse : Bool}
  {inputSize : Nat}
  {execution : TraceResult (ListSortImplResult κ ν)}
  {openState : MergeState κ ν}
  {openForest closedForest : List SpannedMergeTree}
  {scanEvents collapseEvents : List PolicyEvent}
  {collapsed : MergeForceCollapseResult κ ν}
  {witness : ListSortScanStrongWitness input initialForest reverse inputSize execution openState openForest closedForest scanEvents collapseEvents collapsed} :
-- imply
  PowerOpenForestValid input openForest := by
-- proof
  apply CPythonListsort.ListSortScanStrongWitness.openPowerValid witness

/--
[ListSortScanPolicyReplayPost.formedLengthRelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ListSortMergePolicy.lean)
-/
@[path]
private lemma formedLengthRelation_eq
  {κ : Type u}
  {ν : Type v}
  {input : RunSpan}
  {initialForest : List SpannedMergeTree}
  {fuel : Nat}
  {state : MergeState κ ν}
  {lo remaining : Nat}
  {reverse : Bool}
  {inputSize : Nat}
  {post : ListSortScanPolicyReplayPost input initialForest fuel state lo remaining reverse inputSize} :
-- imply
  ∀ push, PolicyEvent.formed push ∈ (listSortScanTraced? fuel state lo remaining reverse inputSize).trace.policyEvents → FormedLengthRelation push := by
-- proof
  apply CPythonListsort.ListSortScanPolicyReplayPost.formedLengthRelation post


-- created on 2026-10-23
