import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.CPythonListsort.Code.Transcription.MergeAt
open CPythonListsort


namespace CPythonListsort

/--
[mergeAt_bindOptionAcross_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean)
-/
@[path]
lemma mergeAt_bindOptionAcross_none
  {κ : Type u}
  {ν : Type v}
  {α : Type w}
  {β : Type x}
  {next : α → Option β} :
-- imply
  bindOptionAcross none next = none :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeAt_bindOptionAcross_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean)
-/
@[path]
lemma mergeAt_bindOptionAcross_some
  {κ : Type u}
  {ν : Type v}
  {α : Type w}
  {β : Type x}
  {value : α}
  {next : α → Option β} :
-- imply
  bindOptionAcross (some value) next = next value :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeAtSuccess_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean)
-/
@[path]
lemma mergeAtSuccess_eq
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  mergeAtSuccess state = { state := state, returnCode := 0, fuelExhausted := false } :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[mergeAtOutOfFuel_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean)
-/
@[path]
lemma mergeAtOutOfFuel_eq
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν} :
-- imply
  mergeAtOutOfFuel state = { state := state, returnCode := -1, fuelExhausted := true } :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[fromMergeLo_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean)
-/
@[path]
lemma fromMergeLo_eq
  {κ : Type u}
  {ν : Type v}
  {result : MergeLoResult κ ν} :
-- imply
  fromMergeLo result = { state := result.state returnCode := result.returnCode fuelExhausted := result.fuelExhausted } :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[fromMergeHi_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean)
-/
@[path]
lemma fromMergeHi_eq
  {κ : Type u}
  {ν : Type v}
  {result : MergeHiResult κ ν} :
-- imply
  fromMergeHi result = { state := result.state returnCode := result.returnCode fuelExhausted := result.fuelExhausted } :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[combinePendingAt_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean)
-/
@[path]
lemma combinePendingAt_eq
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {i : Nat}
  {left right : PendingRun} :
-- imply
  combinePendingAt state i left right = { state with pending := (state.pending.setIfInBounds i { left with len := left.len + right.len }).eraseIdxIfInBounds (i + 1) } :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[combinePendingAt_layoutFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean)
-/
@[path]
private lemma combinePendingAt_layoutFrame (state : MergeState κ ν) (i : Nat)
  (left right : PendingRun) :
  let combined := { left with len := left.len + right.len }
  let combinedState := combinePendingAt state i left right
  combinedState.listlen = state.listlen ∧
    combinedState.basekeys = state.basekeys ∧
    combinedState.data.entries.size = state.data.entries.size ∧
    combinedState.a.hasValues = state.a.hasValues ∧
    combinedState.alloced = state.alloced ∧
    combinedState.pending =
      (state.pending.setIfInBounds i combined).eraseIdxIfInBounds (i + 1) := by
  simp [combinePendingAt]
attribute [aesop safe forward] mergeLo_layout_frame_of_eq_some
  mergeHi_layoutFrame_of_eq_some

end CPythonListsort

namespace CPythonListsort

/--
[prepareMergeAt_lo_callsite_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean)
-/
@[path]
lemma prepareMergeAt_lo_callsite_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {pre : MergeState κ ν}
  {i : Nat}
  {call : MergeAtCall κ ν}
-- given
  (h : prepareMergeAt? pre i = some (.mergeLo call)) :
-- imply
  MergeAtCallsiteEvidence pre i call ∧ call.na ≤ call.nb := by
-- proof
  simp only [prepareMergeAt?, bindOptionAcross] at h
  split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try cases h
  all_goals
    aesop (config := {
      enableSimp := true, maxRuleApplications := 200,
      warnOnNonterminal := false })
  all_goals constructor <;> simp_all
  all_goals omega
set_option linter.flexible false in
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in

end CPythonListsort

namespace CPythonListsort

/--
[prepareMergeAt_hi_callsite_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean)
-/
@[path]
lemma prepareMergeAt_hi_callsite_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {pre : MergeState κ ν}
  {i : Nat}
  {call : MergeAtCall κ ν}
-- given
  (h : prepareMergeAt? pre i = some (.mergeHi call)) :
-- imply
  MergeAtCallsiteEvidence pre i call ∧ call.nb < call.na := by
-- proof
  simp only [prepareMergeAt?, bindOptionAcross] at h
  split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try cases h
  all_goals
    aesop (config := {
      enableSimp := true, maxRuleApplications := 200,
      warnOnNonterminal := false })
  all_goals try omega
  all_goals constructor <;> simp_all
  all_goals omega
set_option linter.flexible false in
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 10000 in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[prepareMergeAt_frame_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean)
-/
@[path]
private lemma prepareMergeAt_frame_of_eq_some
  (state : MergeState κ ν) (i : Nat) (prepared : MergeAtPreparation κ ν)
  (h : prepareMergeAt? state i = some prepared) :
  ∃ left right,
    state.pending[i]? = some left ∧
    state.pending[i + 1]? = some right ∧
    prepared.state.listlen = state.listlen ∧
    prepared.state.basekeys = state.basekeys ∧
    prepared.state.data.entries.size = state.data.entries.size ∧
    prepared.state.pending =
      (state.pending.setIfInBounds i
        { left with len := left.len + right.len }).eraseIdxIfInBounds (i + 1) := by
  simp only [prepareMergeAt?, bindOptionAcross] at h
  split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try split at h <;> try simp at h
  all_goals try cases h
  all_goals
    aesop (config := {
      enableSimp := false, maxRuleApplications := 100,
      warnOnNonterminal := false })
set_option linter.flexible false in

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[finishMergeAtPreparation_layoutFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean)
-/
@[path]
private lemma finishMergeAtPreparation_layoutFrame
  (prepared : MergeAtPreparation κ ν) (result : MergeAtResult κ ν)
  (h : finishMergeAtPreparation? prepared = some result) :
  result.state.listlen = prepared.state.listlen ∧
    result.state.basekeys = prepared.state.basekeys ∧
    result.state.data.entries.size = prepared.state.data.entries.size ∧
    result.state.pending = prepared.state.pending := by
  cases prepared with
  | finished preparedResult =>
    have hresult : preparedResult = result := by
      simpa [finishMergeAtPreparation?] using Option.some.inj h
    subst result
    simp [MergeAtPreparation.state]
  | mergeLo call =>
    simp only [finishMergeAtPreparation?] at h
    split at h <;> try simp at h
    rename_i mergeResult hmerge
    rw [← h]
    simpa [fromMergeLo, MergeAtPreparation.state] using
      mergeLo_layout_frame_of_eq_some call.state call.ssa call.ssb call.na
        call.nb mergeResult hmerge
  | mergeHi call =>
    simp only [finishMergeAtPreparation?] at h
    split at h <;> try simp at h
    rename_i mergeResult hmerge
    rw [← h]
    simpa [fromMergeHi, MergeAtPreparation.state] using
      mergeHi_layoutFrame_of_eq_some call.state call.ssa call.ssb call.na
        call.nb mergeResult hmerge
set_option maxHeartbeats 5000000 in

end CPythonListsort

namespace CPythonListsort

/--
[mergeAt_pending_frame_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean)
-/
@[path]
lemma mergeAt_pending_frame_of_eq_some
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {i : Nat}
  {result : MergeAtResult κ ν}
-- given
  (h : mergeAt? state i = some result) :
-- imply
  ∃ left right, state.pending[i]? = some left ∧ state.pending[i + 1]? = some right ∧ result.state.listlen = state.listlen ∧ result.state.basekeys = state.basekeys ∧ result.state.data.entries.size = state.data.entries.size ∧ result.state.pending = (state.pending.setIfInBounds i { left with len := left.len + right.len }).eraseIdxIfInBounds (i + 1) := by
-- proof
  unfold mergeAt? at h
  cases hprepare : prepareMergeAt? state i with
  | none => simp [bindOptionAcross, hprepare] at h
  | some prepared =>
    have hfinish : finishMergeAtPreparation? prepared = some result := by
      simpa [bindOptionAcross, hprepare] using h
    rcases prepareMergeAt_frame_of_eq_some state i prepared hprepare with
      ⟨left, right, hleft, hright, hlistlen, hbasekeys, hdataSize,
        hpending⟩
    rcases finishMergeAtPreparation_layoutFrame prepared result hfinish with
      ⟨hresultListlen, hresultBasekeys, hresultDataSize, hresultPending⟩
    exact
      ⟨left, right, hleft, hright, hresultListlen.trans hlistlen,
        hresultBasekeys.trans hbasekeys, hresultDataSize.trans hdataSize,
        hresultPending.trans hpending⟩

end CPythonListsort

namespace CPythonListsort

/--
[mergeAt_slide_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Transcription/MergeAt.lean)
-/
@[path]
lemma mergeAt_slide_regression
  {κ : Type u}
  {ν : Type v} :
-- imply
  (mergeAt? mergeAtSlideExampleState 0).map (fun result => (result.returnCode, result.fuelExhausted, result.state.pending.toList)) = some (0, false, [{ base := 0, len := 2, power := some 4 }, { base := 2, len := 1, power := none }]) := by
-- proof
  native_decide

end CPythonListsort


-- created on 2026-10-23
