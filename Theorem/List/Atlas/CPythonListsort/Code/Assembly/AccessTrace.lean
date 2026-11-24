module

public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.CPythonListsort.Code.Assembly.AccessTrace.Part6
public import Def.CPythonListsort.Code.Assembly.AccessTrace.Part7
public import Def.CPythonListsort.Code.Assembly.AccessTrace.Part9

public section

open CPythonListsort.MergeMemorySnapshot CPythonListsort.AccessTrace


namespace CPythonListsort.AccessEvent

public instance {event : AccessEvent} : Decidable (InBounds event) :=
  inferInstanceAs (Decidable (0 ≤ event.index ∧ event.index < Int.ofNat event.extent))

public instance {event : AccessEvent} : Decidable (TempPayloadLive event) := by
  unfold TempPayloadLive
  cases event.region <;> infer_instance

end CPythonListsort.AccessEvent

namespace CPythonListsort.AccessTrace

public instance {trace : AccessTrace} : Decidable (allAccessesInBounds trace) := by
  unfold allAccessesInBounds
  infer_instance

public instance {trace : AccessTrace} : Decidable (tempPayloadAccessesLive trace) := by
  unfold tempPayloadAccessesLive
  infer_instance

end CPythonListsort.AccessTrace


namespace CPythonListsort.MergeMemorySnapshot

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma ext
  {left right : MergeMemorySnapshot}
-- given
  (backing : left.backing = right.backing)
  (hasValues : left.hasValues = right.hasValues)
  (cellsSize : left.cellsSize = right.cellsSize)
  (alloced : left.alloced = right.alloced)
  (physicalSlots : left.physicalSlots = right.physicalSlots)
  (mainValuePresent : left.mainValuePresent = right.mainValuePresent) :
-- imply
  left = right := by
-- proof
  cases left
  cases right
  simp_all

end CPythonListsort.MergeMemorySnapshot

namespace CPythonListsort.AccessTrace

/--
[compose_empty_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma compose_empty_left
  {trace : AccessTrace} :
-- imply
  compose empty trace = trace := by
-- proof
  cases trace
  simp [compose, empty]

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[compose_empty_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma compose_empty_right
  {trace : AccessTrace} :
-- imply
  compose trace empty = trace := by
-- proof
  cases trace
  simp [compose, empty]

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[compose_assoc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma compose_assoc
  {first second third : AccessTrace} :
-- imply
  compose (compose first second) third = compose first (compose second third) := by
-- proof
  cases first
  cases second
  cases third
  simp [compose, List.append_assoc, Bool.or_assoc]

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[fuelExhausted_compose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma fuelExhausted_compose
  {earlier later : AccessTrace} :
-- imply
  (compose earlier later).fuelExhausted = (earlier.fuelExhausted || later.fuelExhausted) := by
-- proof
  rfl

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[policyEvents_compose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma policyEvents_compose
  {earlier later : AccessTrace} :
-- imply
  (compose earlier later).policyEvents = earlier.policyEvents ++ later.policyEvents := by
-- proof
  rfl

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[policyEvents_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma policyEvents_empty :
-- imply
  empty.policyEvents = [] := by
-- proof
  rfl

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[policyEvents_singletonPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma policyEvents_singletonPolicyEvent
  {event : PolicyEvent} :
-- imply
  (singletonPolicyEvent event).policyEvents = [event] := by
-- proof
  rfl

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[policyEvents_singletonFormedRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma policyEvents_singletonFormedRun
  {event : PendingPushEvent} :
-- imply
  (singletonFormedRun event).policyEvents = [.formed event] := by
-- proof
  rfl

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[fuelExhausted_compose_eq_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma fuelExhausted_compose_eq_false
  {earlier later : AccessTrace} :
-- imply
  (compose earlier later).fuelExhausted = false ↔ earlier.fuelExhausted = false ∧ later.fuelExhausted = false := by
-- proof
  cases hEarlier : earlier.fuelExhausted <;>
    cases hLater : later.fuelExhausted <;>
    simp [compose, hEarlier, hLater]

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[allAccessesInBounds_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma allAccessesInBounds_empty :
-- imply
  empty.allAccessesInBounds := by
-- proof
  simp [allAccessesInBounds, empty]

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

public lemma allAccessesInBounds_compose
    {earlier later : AccessTrace} :
    (compose earlier later).allAccessesInBounds ↔
      earlier.allAccessesInBounds ∧ later.allAccessesInBounds := by
  simp [allAccessesInBounds, compose]
  constructor
  · intro h
    exact ⟨fun event he => h event (.inl he), fun event he => h event (.inr he)⟩
  · rintro ⟨h₁, h₂⟩ event hmem
    cases hmem with
    | inl he => exact h₁ event he
    | inr he => exact h₂ event he

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

public lemma tempPayloadAccessesLive_empty :
    empty.tempPayloadAccessesLive := by
  simp [tempPayloadAccessesLive, empty]

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

public lemma tempPayloadAccessesLive_compose
    {earlier later : AccessTrace} :
    (compose earlier later).tempPayloadAccessesLive ↔
      earlier.tempPayloadAccessesLive ∧ later.tempPayloadAccessesLive := by
  simp [tempPayloadAccessesLive, compose]
  constructor
  · intro h
    exact ⟨fun event he => h event (.inl he), fun event he => h event (.inr he)⟩
  · rintro ⟨h₁, h₂⟩ event hmem
    cases hmem with
    | inl he => exact h₁ event he
    | inr he => exact h₂ event he

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[stackDepthMax_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma stackDepthMax_empty :
-- imply
  empty.stackDepthMax = 0 := by
-- proof
  rfl

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[stackDepthMax_singletonPushDepth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma stackDepthMax_singletonPushDepth
  {depth : Nat} :
-- imply
  (singletonPushDepth depth).stackDepthMax = depth := by
-- proof
  simp [stackDepthMax, singletonPushDepth]

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[stackDepthMax_singletonFormedRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma stackDepthMax_singletonFormedRun
  {event : PendingPushEvent} :
-- imply
  (singletonFormedRun event).stackDepthMax = event.depthAfter := by
-- proof
  simp [stackDepthMax, singletonFormedRun]

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[foldl_max_eq_max_foldl_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
private theorem foldl_max_eq_max_foldl_zero (depths : List Nat) (initial : Nat) :
  depths.foldl Nat.max initial =
    Nat.max initial (depths.foldl Nat.max 0) := by
  induction depths generalizing initial with
  | nil => simp
  | cons depth depths ih =>
    simp only [List.foldl_cons]
    rw [ih (Nat.max initial depth), ih (Nat.max 0 depth)]
    have hZero : Nat.max 0 depth = depth := Nat.max_eq_right (Nat.zero_le depth)
    rw [hZero]
    ac_rfl

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[stackDepthMax_compose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma stackDepthMax_compose
  {earlier later : AccessTrace} :
-- imply
  (compose earlier later).stackDepthMax = Nat.max earlier.stackDepthMax later.stackDepthMax := by
-- proof
  simp only [stackDepthMax, compose, List.foldl_append]
  exact foldl_max_eq_max_foldl_zero later.pushDepths
    (earlier.pushDepths.foldl Nat.max 0)

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_pure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_pure
  {value : α} :
-- imply
  (pure value).erase = some value := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_failure :
-- imply
  (failure : TraceResult α).erase = none := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_map
  {transform : α → β}
  {current : TraceResult α} :
-- imply
  (current.map transform).erase = current.erase.map transform := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[result_prependMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma result_prependMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.prependMemoryEvent event).result = current.result := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[result_appendMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma result_appendMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.appendMemoryEvent event).result = current.result := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_prependMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_prependMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.prependMemoryEvent event).erase = current.erase := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_appendMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_appendMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.appendMemoryEvent event).erase = current.erase := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[result_recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma result_recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent} :
-- imply
  (current.recordSuccessMemoryEvent event).result = current.result := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, appendMemoryEvent, AccessTrace.compose,
      AccessTrace.singletonMemoryEvent, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent} :
-- imply
  (current.recordSuccessMemoryEvent event).erase = current.erase := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, appendMemoryEvent, TraceResult.erase, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[result_appendPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma result_appendPolicyEvent
  {current : TraceResult α}
  {event : PolicyEvent} :
-- imply
  (current.appendPolicyEvent event).result = current.result := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_appendPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_appendPolicyEvent
  {current : TraceResult α}
  {event : PolicyEvent} :
-- imply
  (current.appendPolicyEvent event).erase = current.erase := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[result_recordSuccessPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma result_recordSuccessPolicyEvent
  {current : TraceResult α}
  {event : α → PolicyEvent} :
-- imply
  (current.recordSuccessPolicyEvent event).result = current.result := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, appendPolicyEvent, AccessTrace.compose,
      AccessTrace.singletonPolicyEvent, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_recordSuccessPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_recordSuccessPolicyEvent
  {current : TraceResult α}
  {event : α → PolicyEvent} :
-- imply
  (current.recordSuccessPolicyEvent event).erase = current.erase := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, appendPolicyEvent, TraceResult.erase, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[accesses_prependMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma accesses_prependMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.prependMemoryEvent event).trace.accesses = current.trace.accesses := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[accesses_appendMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma accesses_appendMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.appendMemoryEvent event).trace.accesses = current.trace.accesses := by
-- proof
  simp [appendMemoryEvent, AccessTrace.compose,
    AccessTrace.singletonMemoryEvent]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[pushDepths_prependMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma pushDepths_prependMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.prependMemoryEvent event).trace.pushDepths = current.trace.pushDepths := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[pushDepths_appendMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma pushDepths_appendMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.appendMemoryEvent event).trace.pushDepths = current.trace.pushDepths := by
-- proof
  simp [appendMemoryEvent, AccessTrace.compose,
    AccessTrace.singletonMemoryEvent]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[memoryEvents_prependMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma memoryEvents_prependMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.prependMemoryEvent event).trace.memoryEvents = event :: current.trace.memoryEvents := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[memoryEvents_appendMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma memoryEvents_appendMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.appendMemoryEvent event).trace.memoryEvents = current.trace.memoryEvents ++ [event] := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[memoryEvents_recordSuccessMemoryEvent_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma memoryEvents_recordSuccessMemoryEvent_of_eq_some
  {current : TraceResult α}
  {event : α → MergeMemoryEvent}
  {value : α}
-- given
  (hresult : current.result = some value) :
-- imply
  (current.recordSuccessMemoryEvent event).trace.memoryEvents = current.trace.memoryEvents ++ [event value] := by
-- proof
  simp [recordSuccessMemoryEvent, appendMemoryEvent, AccessTrace.compose, AccessTrace.singletonMemoryEvent, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[policyEvents_prependMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma policyEvents_prependMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.prependMemoryEvent event).trace.policyEvents = current.trace.policyEvents := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[policyEvents_appendMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma policyEvents_appendMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.appendMemoryEvent event).trace.policyEvents = current.trace.policyEvents := by
-- proof
  simp [appendMemoryEvent, AccessTrace.compose,
    AccessTrace.singletonMemoryEvent]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[policyEvents_recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma policyEvents_recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent} :
-- imply
  (current.recordSuccessMemoryEvent event).trace.policyEvents = current.trace.policyEvents := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, appendMemoryEvent, AccessTrace.compose,
      AccessTrace.singletonMemoryEvent, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[policyEvents_appendPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma policyEvents_appendPolicyEvent
  {current : TraceResult α}
  {event : PolicyEvent} :
-- imply
  (current.appendPolicyEvent event).trace.policyEvents = current.trace.policyEvents ++ [event] := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[policyEvents_recordSuccessPolicyEvent_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma policyEvents_recordSuccessPolicyEvent_of_eq_some
  {current : TraceResult α}
  {event : α → PolicyEvent}
  {value : α}
-- given
  (hresult : current.result = some value) :
-- imply
  (current.recordSuccessPolicyEvent event).trace.policyEvents = current.trace.policyEvents ++ [event value] := by
-- proof
  simp [recordSuccessPolicyEvent, appendPolicyEvent, AccessTrace.compose, AccessTrace.singletonPolicyEvent, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[policyEvents_recordSuccessPolicyEvent_of_eq_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma policyEvents_recordSuccessPolicyEvent_of_eq_none
  {current : TraceResult α}
  {event : α → PolicyEvent}
-- given
  (hresult : current.result = none) :
-- imply
  (current.recordSuccessPolicyEvent event).trace.policyEvents = current.trace.policyEvents := by
-- proof
  simp [recordSuccessPolicyEvent, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[fuelExhausted_prependMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma fuelExhausted_prependMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.prependMemoryEvent event).trace.fuelExhausted = current.trace.fuelExhausted := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[fuelExhausted_appendMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma fuelExhausted_appendMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.appendMemoryEvent event).trace.fuelExhausted = current.trace.fuelExhausted := by
-- proof
  simp [appendMemoryEvent, AccessTrace.compose,
    AccessTrace.singletonMemoryEvent]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[accesses_recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma accesses_recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent} :
-- imply
  (current.recordSuccessMemoryEvent event).trace.accesses = current.trace.accesses := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, appendMemoryEvent, AccessTrace.compose, AccessTrace.singletonMemoryEvent, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[pushDepths_recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma pushDepths_recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent} :
-- imply
  (current.recordSuccessMemoryEvent event).trace.pushDepths = current.trace.pushDepths := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, appendMemoryEvent, AccessTrace.compose, AccessTrace.singletonMemoryEvent, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[fuelExhausted_recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma fuelExhausted_recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent} :
-- imply
  (current.recordSuccessMemoryEvent event).trace.fuelExhausted = current.trace.fuelExhausted := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, appendMemoryEvent, AccessTrace.compose, AccessTrace.singletonMemoryEvent, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[allAccessesInBounds_recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma allAccessesInBounds_recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent} :
-- imply
  (current.recordSuccessMemoryEvent event).trace.allAccessesInBounds ↔ current.trace.allAccessesInBounds := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, appendMemoryEvent, AccessTrace.compose, AccessTrace.singletonMemoryEvent, AccessTrace.allAccessesInBounds, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[tempPayloadAccessesLive_recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma tempPayloadAccessesLive_recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent} :
-- imply
  (current.recordSuccessMemoryEvent event).trace.tempPayloadAccessesLive ↔ current.trace.tempPayloadAccessesLive := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, appendMemoryEvent, AccessTrace.compose, AccessTrace.singletonMemoryEvent, AccessTrace.tempPayloadAccessesLive, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[stackDepthMax_prependMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma stackDepthMax_prependMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.prependMemoryEvent event).trace.stackDepthMax = current.trace.stackDepthMax := by
-- proof
  simp only [prependMemoryEvent, AccessTrace.stackDepthMax,
    AccessTrace.compose, AccessTrace.singletonMemoryEvent, List.nil_append]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[stackDepthMax_appendMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma stackDepthMax_appendMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.appendMemoryEvent event).trace.stackDepthMax = current.trace.stackDepthMax := by
-- proof
  simp only [appendMemoryEvent, AccessTrace.stackDepthMax,
    AccessTrace.compose, AccessTrace.singletonMemoryEvent, List.append_nil]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[stackDepthMax_recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma stackDepthMax_recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent} :
-- imply
  (current.recordSuccessMemoryEvent event).trace.stackDepthMax = current.trace.stackDepthMax := by
-- proof
  cases hresult : current.result
  · simp [recordSuccessMemoryEvent, hresult]
  · simp [recordSuccessMemoryEvent, hresult]
    exact stackDepthMax_appendMemoryEvent

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[accesses_appendPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma accesses_appendPolicyEvent
  {current : TraceResult α}
  {event : PolicyEvent} :
-- imply
  (current.appendPolicyEvent event).trace.accesses = current.trace.accesses := by
-- proof
  simp [appendPolicyEvent, AccessTrace.compose,
    AccessTrace.singletonPolicyEvent]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[pushDepths_appendPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma pushDepths_appendPolicyEvent
  {current : TraceResult α}
  {event : PolicyEvent} :
-- imply
  (current.appendPolicyEvent event).trace.pushDepths = current.trace.pushDepths := by
-- proof
  simp [appendPolicyEvent, AccessTrace.compose,
    AccessTrace.singletonPolicyEvent]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[memoryEvents_appendPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma memoryEvents_appendPolicyEvent
  {current : TraceResult α}
  {event : PolicyEvent} :
-- imply
  (current.appendPolicyEvent event).trace.memoryEvents = current.trace.memoryEvents := by
-- proof
  simp [appendPolicyEvent, AccessTrace.compose,
    AccessTrace.singletonPolicyEvent]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[fuelExhausted_appendPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma fuelExhausted_appendPolicyEvent
  {current : TraceResult α}
  {event : PolicyEvent} :
-- imply
  (current.appendPolicyEvent event).trace.fuelExhausted = current.trace.fuelExhausted := by
-- proof
  simp [appendPolicyEvent, AccessTrace.compose,
    AccessTrace.singletonPolicyEvent]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[accesses_recordSuccessPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma accesses_recordSuccessPolicyEvent
  {current : TraceResult α}
  {event : α → PolicyEvent} :
-- imply
  (current.recordSuccessPolicyEvent event).trace.accesses = current.trace.accesses := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, appendPolicyEvent, AccessTrace.compose,
      AccessTrace.singletonPolicyEvent, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[pushDepths_recordSuccessPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma pushDepths_recordSuccessPolicyEvent
  {current : TraceResult α}
  {event : α → PolicyEvent} :
-- imply
  (current.recordSuccessPolicyEvent event).trace.pushDepths = current.trace.pushDepths := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, appendPolicyEvent, AccessTrace.compose, AccessTrace.singletonPolicyEvent, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[memoryEvents_recordSuccessPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma memoryEvents_recordSuccessPolicyEvent
  {current : TraceResult α}
  {event : α → PolicyEvent} :
-- imply
  (current.recordSuccessPolicyEvent event).trace.memoryEvents = current.trace.memoryEvents := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, appendPolicyEvent, AccessTrace.compose, AccessTrace.singletonPolicyEvent, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[fuelExhausted_recordSuccessPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma fuelExhausted_recordSuccessPolicyEvent
  {current : TraceResult α}
  {event : α → PolicyEvent} :
-- imply
  (current.recordSuccessPolicyEvent event).trace.fuelExhausted = current.trace.fuelExhausted := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, appendPolicyEvent, AccessTrace.compose, AccessTrace.singletonPolicyEvent, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[allAccessesInBounds_recordSuccessPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma allAccessesInBounds_recordSuccessPolicyEvent
  {current : TraceResult α}
  {event : α → PolicyEvent} :
-- imply
  (current.recordSuccessPolicyEvent event).trace.allAccessesInBounds ↔ current.trace.allAccessesInBounds := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, appendPolicyEvent, AccessTrace.compose, AccessTrace.singletonPolicyEvent, AccessTrace.allAccessesInBounds, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[tempPayloadAccessesLive_recordSuccessPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma tempPayloadAccessesLive_recordSuccessPolicyEvent
  {current : TraceResult α}
  {event : α → PolicyEvent} :
-- imply
  (current.recordSuccessPolicyEvent event).trace.tempPayloadAccessesLive ↔ current.trace.tempPayloadAccessesLive := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, appendPolicyEvent, AccessTrace.compose, AccessTrace.singletonPolicyEvent, AccessTrace.tempPayloadAccessesLive, hresult]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[stackDepthMax_appendPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma stackDepthMax_appendPolicyEvent
  {current : TraceResult α}
  {event : PolicyEvent} :
-- imply
  (current.appendPolicyEvent event).trace.stackDepthMax = current.trace.stackDepthMax := by
-- proof
  simp only [appendPolicyEvent, AccessTrace.stackDepthMax,
    AccessTrace.compose, AccessTrace.singletonPolicyEvent, List.append_nil]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[stackDepthMax_recordSuccessPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma stackDepthMax_recordSuccessPolicyEvent
  {current : TraceResult α}
  {event : α → PolicyEvent} :
-- imply
  (current.recordSuccessPolicyEvent event).trace.stackDepthMax = current.trace.stackDepthMax := by
-- proof
  cases hresult : current.result
  · simp [recordSuccessPolicyEvent, hresult]
  · simp [recordSuccessPolicyEvent, hresult]
    exact stackDepthMax_appendPolicyEvent

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_bind
  {current : TraceResult α}
  {next : α → TraceResult β} :
-- imply
  (current.bind next).erase = current.erase.bind (fun value => (next value).erase) := by
-- proof
  cases current with
  | mk result trace =>
    cases result <;> rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[memoryEvents_bind_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma memoryEvents_bind_eq_nil
  {current : TraceResult α}
  {next : α → TraceResult β}
-- given
  (hcurrent : current.trace.memoryEvents = [])
  (hnext : ∀ value, (next value).trace.memoryEvents = []) :
-- imply
  (current.bind next).trace.memoryEvents = [] := by
-- proof
  rw [TraceResult.bind]
  cases hresult : current.result with
  | none => exact hcurrent
  | some value =>
    simp [AccessTrace.compose, hcurrent, hnext value]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[policyEvents_bind_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma policyEvents_bind_eq_nil
  {current : TraceResult α}
  {next : α → TraceResult β}
-- given
  (hcurrent : current.trace.policyEvents = [])
  (hnext : ∀ value, (next value).trace.policyEvents = []) :
-- imply
  (current.bind next).trace.policyEvents = [] := by
-- proof
  rw [TraceResult.bind]
  cases hresult : current.result with
  | none => exact hcurrent
  | some value =>
    simp [AccessTrace.compose, hcurrent, hnext value]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[memoryEvents_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma memoryEvents_map
  {current : TraceResult α}
  {transform : α → β} :
-- imply
  (current.map transform).trace.memoryEvents = current.trace.memoryEvents := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[policyEvents_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma policyEvents_map
  {current : TraceResult α}
  {transform : α → β} :
-- imply
  (current.map transform).trace.policyEvents = current.trace.policyEvents := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[policyEvents_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma policyEvents_bind
  {current : TraceResult α}
  {next : α → TraceResult β} :
-- imply
  (current.bind next).trace.policyEvents =
    match current.result with
    | none => current.trace.policyEvents
    | some value => current.trace.policyEvents ++ (next value).trace.policyEvents := by
-- proof
  rw [TraceResult.bind]
  cases current.result <;> simp [AccessTrace.compose]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_markFuelExhausted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_markFuelExhausted
  {current : TraceResult α} :
-- imply
  current.markFuelExhausted.erase = current.erase := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[trace_captureAccess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma trace_captureAccess
  {kind : AccessKind}
  {region : AccessRegion}
  {index : Int}
  {extent : Nat}
  {result : Option α} :
-- imply
  (captureAccess kind region index extent result).trace = AccessTrace.singletonAccess kind region index extent := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[trace_arrayRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma trace_arrayRead
  {region : AccessRegion}
  {array : Array α}
  {index : Int} :
-- imply
  (arrayRead? region array index).trace = AccessTrace.singletonAccess .read region index array.size := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[trace_arrayWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma trace_arrayWrite
  {region : AccessRegion}
  {array : Array α}
  {index : Int}
  {value : α} :
-- imply
  (arrayWrite? region array index value).trace = AccessTrace.singletonAccess .write region index array.size := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_captureAccess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_captureAccess
  {kind : AccessKind}
  {region : AccessRegion}
  {index : Int}
  {extent : Nat}
  {result : Option α} :
-- imply
  (captureAccess kind region index extent result).erase = result := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_arrayRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_arrayRead
  {region : AccessRegion}
  {array : Array α}
  {index : Int} :
-- imply
  (arrayRead? region array index).erase = if 0 ≤ index then array[index.toNat]? else none := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_arrayWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_arrayWrite
  {region : AccessRegion}
  {array : Array α}
  {index : Int}
  {value : α} :
-- imply
  (arrayWrite? region array index value).erase = if 0 ≤ index ∧ index.toNat < array.size then some (array.setIfInBounds index.toNat value) else none := by
-- proof
  rfl
/-! ## State-derived access wrappers -/

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[trace_tempPayloadRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma trace_tempPayloadRead
  {storage : TempStorage κ ν}
  {index : Int} :
-- imply
  (tempPayloadRead? storage index).trace = AccessTrace.singletonAccess .read (.tempPayload storage.backing) index storage.cells.size := by
-- proof
  by_cases hNonnegative : 0 ≤ index
  · cases hCell : storage.cells[index.toNat]? with
    | none =>
      simp [tempPayloadRead?, TraceResult.bind, arrayRead?, captureAccess,
        hNonnegative, hCell]
    | some cell =>
      cases cell <;>
        simp [tempPayloadRead?, TraceResult.bind, arrayRead?, captureAccess,
          pure, failure, hNonnegative, hCell, AccessTrace.compose_empty_right]
  · simp [tempPayloadRead?, TraceResult.bind, arrayRead?, captureAccess,
      hNonnegative]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[trace_tempPayloadWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma trace_tempPayloadWrite
  {storage : TempStorage κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν} :
-- imply
  (tempPayloadWrite? storage index entry).trace = AccessTrace.singletonAccess .write (.tempPayload storage.backing) index storage.cells.size := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_tempPayloadRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_tempPayloadRead
  {storage : TempStorage κ ν}
  {index : Int} :
-- imply
  (tempPayloadRead? storage index).erase = if 0 ≤ index then storage.cells[index.toNat]?.bind id else none := by
-- proof
  by_cases hNonnegative : 0 ≤ index
  · cases hCell : storage.cells[index.toNat]? with
    | none =>
      simp [tempPayloadRead?, hNonnegative, hCell, erase_bind, erase_arrayRead]
    | some cell =>
      cases cell <;>
        simp [tempPayloadRead?, hNonnegative, hCell, erase_bind, erase_arrayRead,
          erase_failure, erase_pure]
  · simp [tempPayloadRead?, hNonnegative, erase_bind, erase_arrayRead]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_tempPayloadWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_tempPayloadWrite
  {storage : TempStorage κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν} :
-- imply
  (tempPayloadWrite? storage index entry).erase = if 0 ≤ index ∧ index.toNat < storage.cells.size then some { storage with cells := storage.cells.setIfInBounds index.toNat (some entry) } else none := by
-- proof
  by_cases hBounds : 0 ≤ index ∧ index.toNat < storage.cells.size <;>
    simp [tempPayloadWrite?, hBounds, erase_map, erase_arrayWrite]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_sortSliceKeysRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_sortSliceKeysRead
  {slice : SortSlice κ ν}
  {index : Int} :
-- imply
  (sortSliceKeysRead? slice index).erase = slice.read? index := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_sortSliceValuesRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_sortSliceValuesRead
  {slice : SortSlice κ ν}
  {index : Int} :
-- imply
  (sortSliceValuesRead? slice index).erase = slice.read? index := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_sortSliceKeysWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_sortSliceKeysWrite
  {slice : SortSlice κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν} :
-- imply
  (sortSliceKeysWrite? slice index entry).erase = slice.write? index entry := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_sortSliceValuesWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_sortSliceValuesWrite
  {slice : SortSlice κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν} :
-- imply
  (sortSliceValuesWrite? slice index entry).erase = slice.write? index entry := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[trace_sortSliceKeysRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma trace_sortSliceKeysRead
  {slice : SortSlice κ ν}
  {index : Int} :
-- imply
  (sortSliceKeysRead? slice index).trace = AccessTrace.singletonAccess .read .inputKeys index slice.entries.size := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[trace_sortSliceValuesRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma trace_sortSliceValuesRead
  {slice : SortSlice κ ν}
  {index : Int} :
-- imply
  (sortSliceValuesRead? slice index).trace = AccessTrace.singletonAccess .read .synchronizedValues index slice.entries.size := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[trace_sortSliceKeysWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma trace_sortSliceKeysWrite
  {slice : SortSlice κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν} :
-- imply
  (sortSliceKeysWrite? slice index entry).trace = AccessTrace.singletonAccess .write .inputKeys index slice.entries.size := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[trace_sortSliceValuesWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma trace_sortSliceValuesWrite
  {slice : SortSlice κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν} :
-- imply
  (sortSliceValuesWrite? slice index entry).trace = AccessTrace.singletonAccess .write .synchronizedValues index slice.entries.size := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_pendingRunRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_pendingRunRead
  {state : MergeState κ ν}
  {index : Int} :
-- imply
  (pendingRunRead? state index).erase = if 0 ≤ index then state.pending[index.toNat]? else none := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_pendingRunWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_pendingRunWrite
  {state : MergeState κ ν}
  {index : Int}
  {run : PendingRun} :
-- imply
  (pendingRunWrite? state index run).erase = if 0 ≤ index ∧ index.toNat < state.pending.size then some { state with pending := state.pending.setIfInBounds index.toNat run } else none := by
-- proof
  by_cases hBounds : 0 ≤ index ∧ index.toNat < state.pending.size <;>
    simp [pendingRunWrite?, hBounds, erase_map, erase_arrayWrite]

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[erase_pendingRunPowerWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_pendingRunPowerWrite
  {state : MergeState κ ν}
  {index : Int}
  {power : Nat} :
-- imply
  (pendingRunPowerWrite? state index power).erase = if 0 ≤ index then state.pending[index.toNat]?.map fun top => { state with pending := state.pending.setIfInBounds index.toNat ({ top with power := some power } : PendingRun) } else none := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[trace_pendingRunRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma trace_pendingRunRead
  {state : MergeState κ ν}
  {index : Int} :
-- imply
  (pendingRunRead? state index).trace = AccessTrace.singletonAccess .read .pendingRuns index state.pending.size := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[trace_pendingRunWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma trace_pendingRunWrite
  {state : MergeState κ ν}
  {index : Int}
  {run : PendingRun} :
-- imply
  (pendingRunWrite? state index run).trace = AccessTrace.singletonAccess .write .pendingRuns index state.pending.size := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort.AccessTrace.TraceResult

/--
[trace_pendingRunPowerWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma trace_pendingRunPowerWrite
  {state : MergeState κ ν}
  {index : Int}
  {power : Nat} :
-- imply
  (pendingRunPowerWrite? state index power).trace = AccessTrace.singletonAccess .write .pendingRuns index state.pending.size := by
-- proof
  rfl

end CPythonListsort.AccessTrace.TraceResult

namespace CPythonListsort

/--
[erase_AccessTrace.TraceResult.pushPendingRunTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_AccessTrace.TraceResult.pushPendingRunTraced
  {state : MergeState κ ν}
  {run : PendingRun} :
-- imply
  (AccessTrace.TraceResult.pushPendingRunTraced state run).erase = some { state with pending := state.pending.push run } := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[trace_AccessTrace.TraceResult.pushPendingRunTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma trace_AccessTrace.TraceResult.pushPendingRunTraced
  {state : MergeState κ ν}
  {run : PendingRun} :
-- imply
  (AccessTrace.TraceResult.pushPendingRunTraced state run).trace = AccessTrace.singletonPushDepth (state.pending.size + 1) := by
-- proof
  simp [AccessTrace.TraceResult.pushPendingRunTraced, AccessTrace.singletonPushDepth]

end CPythonListsort

namespace CPythonListsort

/--
[erase_AccessTrace.TraceResult.pushFormedRunTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma erase_AccessTrace.TraceResult.pushFormedRunTraced
  {state : MergeState κ ν}
  {run : PendingRun}
  {naturalLength target remainingBefore : Nat} :
-- imply
  (AccessTrace.TraceResult.pushFormedRunTraced state run naturalLength target remainingBefore).erase = some { state with pending := state.pending.push run } := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[trace_AccessTrace.TraceResult.pushFormedRunTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma trace_AccessTrace.TraceResult.pushFormedRunTraced
  {state : MergeState κ ν}
  {run : PendingRun}
  {naturalLength target remainingBefore : Nat} :
-- imply
  (AccessTrace.TraceResult.pushFormedRunTraced state run naturalLength target remainingBefore).trace = AccessTrace.singletonFormedRun { run := RunSpan.ofPendingRun run, depthAfter := state.pending.size + 1, naturalLength := naturalLength, target := target, remainingBefore := remainingBefore } := by
-- proof
  simp [AccessTrace.TraceResult.pushFormedRunTraced, AccessTrace.singletonFormedRun]

end CPythonListsort

namespace CPythonListsort

/--
[AccessTrace.TraceResult.pushFormedRunTraced_legacyProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma AccessTrace.TraceResult.pushFormedRunTraced_legacyProjection
  {state : MergeState κ ν}
  {run : PendingRun}
  {naturalLength target remainingBefore : Nat} :
-- imply
  (AccessTrace.TraceResult.pushFormedRunTraced state run naturalLength target remainingBefore).erase = (AccessTrace.TraceResult.pushPendingRunTraced state run).erase ∧ (AccessTrace.TraceResult.pushFormedRunTraced state run naturalLength target remainingBefore).trace.accesses = (AccessTrace.TraceResult.pushPendingRunTraced state run).trace.accesses ∧ (AccessTrace.TraceResult.pushFormedRunTraced state run naturalLength target remainingBefore).trace.pushDepths = (AccessTrace.TraceResult.pushPendingRunTraced state run).trace.pushDepths ∧ (AccessTrace.TraceResult.pushFormedRunTraced state run naturalLength target remainingBefore).trace.memoryEvents = (AccessTrace.TraceResult.pushPendingRunTraced state run).trace.memoryEvents ∧ (AccessTrace.TraceResult.pushFormedRunTraced state run naturalLength target remainingBefore).trace.fuelExhausted = (AccessTrace.TraceResult.pushPendingRunTraced state run).trace.fuelExhausted := by
-- proof
  refine ⟨rfl, ?_⟩
  simp [AccessTrace.TraceResult.pushFormedRunTraced, AccessTrace.TraceResult.pushPendingRunTraced,
    AccessTrace.singletonFormedRun, AccessTrace.singletonPushDepth]

end CPythonListsort

namespace CPythonListsort

/--
[AccessTrace.TraceResult.pushFormedRunTraced_policyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma AccessTrace.TraceResult.pushFormedRunTraced_policyEvent
  {state : MergeState κ ν}
  {run : PendingRun}
  {naturalLength target remainingBefore : Nat} :
-- imply
  (AccessTrace.TraceResult.pushFormedRunTraced state run naturalLength target remainingBefore).trace.policyEvents = [.formed { run := RunSpan.ofPendingRun run, depthAfter := state.pending.size + 1, naturalLength := naturalLength, target := target, remainingBefore := remainingBefore }] ∧ (AccessTrace.TraceResult.pushFormedRunTraced state run naturalLength target remainingBefore).trace.pushDepths = [state.pending.size + 1] := by
-- proof
  simp [trace_AccessTrace.TraceResult.pushFormedRunTraced, AccessTrace.singletonFormedRun]

end CPythonListsort

namespace CPythonListsort

/--
[forcedPushAtCapacity_records65](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma forcedPushAtCapacity_records65 :
-- imply
  AccessTrace.TraceResult.accessTraceForcedPush.result.map Array.size = some 65 ∧ AccessTrace.TraceResult.accessTraceForcedPush.trace.pushDepths = [65] ∧ AccessTrace.TraceResult.accessTraceForcedPush.trace.stackDepthMax = 65 := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[AccessTrace.TraceResult.pushPendingRunTraced_at_capacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma pushPendingRunTraced_at_capacity
  {state : MergeState κ ν}
  {run : PendingRun}
-- given
  (hDepth : state.pending.size = MAX_MERGE_PENDING) :
-- imply
  (AccessTrace.TraceResult.pushPendingRunTraced state run).result.map (fun pushed => pushed.pending.size) = some 65 ∧ (AccessTrace.TraceResult.pushPendingRunTraced state run).trace.pushDepths = [65] ∧ (AccessTrace.TraceResult.pushPendingRunTraced state run).trace.stackDepthMax = 65 := by
-- proof
  simp [AccessTrace.TraceResult.pushPendingRunTraced, hDepth, MAX_MERGE_PENDING,
    AccessTrace.singletonPushDepth, AccessTrace.stackDepthMax]

end CPythonListsort

namespace CPythonListsort

/--
[AccessTrace.TraceResult.rejectedReleasedTempRead_is_observable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma rejectedReleasedTempRead_is_observable :
-- imply
  AccessTrace.TraceResult.rejectedReleasedTempRead.result = none ∧ AccessTrace.TraceResult.rejectedReleasedTempRead.trace.accesses = [{ kind := .read, region := .tempPayload .released, index := 0, extent := 0 }] ∧ ¬AccessTrace.TraceResult.rejectedReleasedTempRead.trace.allAccessesInBounds ∧ ¬AccessTrace.TraceResult.rejectedReleasedTempRead.trace.tempPayloadAccessesLive := by
-- proof
  -- `decide` cannot unfold unexposed `instDecidableEqAccessEvent.decEq`
  -- (Structure.AccessTrace is not `@[expose]`).
  have htrace :=
    AccessTrace.TraceResult.trace_tempPayloadRead
      (storage := AccessTrace.TraceResult.releasedTempStorage) (index := (0 : Int))
  have herase :=
    AccessTrace.TraceResult.erase_tempPayloadRead
      (storage := AccessTrace.TraceResult.releasedTempStorage) (index := (0 : Int))
  simp [AccessTrace.TraceResult.rejectedReleasedTempRead,
    AccessTrace.TraceResult.releasedTempStorage, AccessTrace.TraceResult.erase,
    AccessTrace.singletonAccess, AccessTrace.allAccessesInBounds,
    AccessTrace.tempPayloadAccessesLive, AccessEvent.InBounds,
    AccessEvent.TempPayloadLive] at htrace herase ⊢
  exact ⟨herase, htrace ▸ rfl, by simp [htrace], by simp [htrace]⟩

end CPythonListsort

namespace CPythonListsort

/--
[AccessTrace.TraceResult.rejectedUninitializedTempRead_is_observable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma rejectedUninitializedTempRead_is_observable :
-- imply
  AccessTrace.TraceResult.rejectedUninitializedTempRead.result = none ∧ AccessTrace.TraceResult.rejectedUninitializedTempRead.trace.accesses = [{ kind := .read, region := .tempPayload .inline, index := 0, extent := 1 }] ∧ AccessTrace.TraceResult.rejectedUninitializedTempRead.trace.allAccessesInBounds ∧ AccessTrace.TraceResult.rejectedUninitializedTempRead.trace.tempPayloadAccessesLive := by
-- proof
  -- `decide` cannot unfold unexposed `instDecidableEqAccessEvent.decEq`
  -- (Structure.AccessTrace is not `@[expose]`).
  have htrace :=
    AccessTrace.TraceResult.trace_tempPayloadRead
      (storage := AccessTrace.TraceResult.uninitializedTempStorage) (index := (0 : Int))
  have herase :=
    AccessTrace.TraceResult.erase_tempPayloadRead
      (storage := AccessTrace.TraceResult.uninitializedTempStorage) (index := (0 : Int))
  simp [AccessTrace.TraceResult.rejectedUninitializedTempRead,
    AccessTrace.TraceResult.uninitializedTempStorage, AccessTrace.TraceResult.erase,
    AccessTrace.singletonAccess, AccessTrace.allAccessesInBounds,
    AccessTrace.tempPayloadAccessesLive, AccessEvent.InBounds,
    AccessEvent.TempPayloadLive] at htrace herase ⊢
  exact ⟨herase, htrace ▸ rfl, by simp [htrace], by simp [htrace]⟩

end CPythonListsort

namespace CPythonListsort

/--
[localTraceComposition_preserves_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
public lemma localTraceComposition_preserves_order :
-- imply
  AccessTrace.TraceResult.orderedAccessRegression.trace.accesses = [{ kind := .read, region := .inputKeys, index := 1, extent := 2 }, { kind := .write, region := .synchronizedValues, index := 0, extent := 2 }] ∧ AccessTrace.TraceResult.orderedAccessRegression.trace.allAccessesInBounds ∧ AccessTrace.TraceResult.orderedAccessRegression.trace.tempPayloadAccessesLive := by
-- proof
  -- `decide` cannot unfold unexposed `instDecidableEqAccessEvent.decEq`
  -- (Structure.AccessTrace is not `@[expose]`).
  have hread_trace :=
    AccessTrace.TraceResult.trace_sortSliceKeysRead
      (slice := AccessTrace.TraceResult.orderedAccessSlice) (index := (1 : Int))
  have hread_erase :=
    AccessTrace.TraceResult.erase_sortSliceKeysRead
      (slice := AccessTrace.TraceResult.orderedAccessSlice) (index := (1 : Int))
  have hread_some :
      (AccessTrace.TraceResult.sortSliceKeysRead?
        AccessTrace.TraceResult.orderedAccessSlice 1).result =
        some { key := 9, value := some 90 } := by
    simpa [AccessTrace.TraceResult.erase, AccessTrace.TraceResult.orderedAccessSlice,
      SortSlice.read?] using hread_erase
  unfold AccessTrace.TraceResult.orderedAccessRegression
  simp only [AccessTrace.TraceResult.bind, hread_some]
  have hwrite_trace :=
    AccessTrace.TraceResult.trace_sortSliceValuesWrite
      (slice := AccessTrace.TraceResult.orderedAccessSlice)
      (index := (0 : Int))
      (entry := { key := 9, value := some 90 })
  rw [hread_trace, hwrite_trace]
  simp [AccessTrace.compose, AccessTrace.singletonAccess,
    AccessTrace.TraceResult.orderedAccessSlice, AccessTrace.allAccessesInBounds,
    AccessTrace.tempPayloadAccessesLive, AccessEvent.InBounds,
    AccessEvent.TempPayloadLive]

end CPythonListsort


-- created on 2026-10-23
