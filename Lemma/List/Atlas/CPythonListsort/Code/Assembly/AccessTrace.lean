import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Assembly.AccessTrace
open CPythonListsort CPythonListsort.MergeMemorySnapshot CPythonListsort.AccessTrace CPythonListsort.TraceResult


namespace CPythonListsort.MergeMemorySnapshot

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma ext
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
lemma compose_empty_left
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
lemma compose_empty_right
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
lemma compose_assoc
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
lemma fuelExhausted_compose
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
lemma policyEvents_compose
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
lemma policyEvents_empty
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
lemma policyEvents_singletonPolicyEvent
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
lemma policyEvents_singletonFormedRun
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
lemma fuelExhausted_compose_eq_false
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
lemma allAccessesInBounds_empty
-- imply
  empty.allAccessesInBounds := by
-- proof
  simp [allAccessesInBounds, empty]

end CPythonListsort.AccessTrace

namespace CPythonListsort.AccessTrace

/--
[stackDepthMax_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma stackDepthMax_empty
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
lemma stackDepthMax_singletonPushDepth
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
lemma stackDepthMax_singletonFormedRun
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
private lemma foldl_max_eq_max_foldl_zero (depths : List Nat) (initial : Nat) :
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
lemma stackDepthMax_compose
  {earlier later : AccessTrace} :
-- imply
  (compose earlier later).stackDepthMax = Nat.max earlier.stackDepthMax later.stackDepthMax := by
-- proof
  simp only [stackDepthMax, compose, List.foldl_append]
  exact foldl_max_eq_max_foldl_zero later.pushDepths
    (earlier.pushDepths.foldl Nat.max 0)

end CPythonListsort.AccessTrace

namespace CPythonListsort.TraceResult

/--
[erase_pure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_pure
  {value : α} :
-- imply
  (pure value).erase = some value := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_failure
-- imply
  (failure : TraceResult α).erase = none := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_map
  {transform : α → β}
  {current : TraceResult α} :
-- imply
  (current.map transform).erase = current.erase.map transform := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[result_prependMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma result_prependMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.prependMemoryEvent event).result = current.result := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[result_appendMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma result_appendMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.appendMemoryEvent event).result = current.result := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_prependMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_prependMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.prependMemoryEvent event).erase = current.erase := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_appendMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_appendMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.appendMemoryEvent event).erase = current.erase := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[result_recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma result_recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent} :
-- imply
  (current.recordSuccessMemoryEvent event).result = current.result := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, hresult]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent} :
-- imply
  (current.recordSuccessMemoryEvent event).erase = current.erase := by
-- proof
  simp [TraceResult.erase]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[result_appendPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma result_appendPolicyEvent
  {current : TraceResult α}
  {event : PolicyEvent} :
-- imply
  (current.appendPolicyEvent event).result = current.result := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_appendPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_appendPolicyEvent
  {current : TraceResult α}
  {event : PolicyEvent} :
-- imply
  (current.appendPolicyEvent event).erase = current.erase := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[result_recordSuccessPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma result_recordSuccessPolicyEvent
  {current : TraceResult α}
  {event : α → PolicyEvent} :
-- imply
  (current.recordSuccessPolicyEvent event).result = current.result := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, hresult]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_recordSuccessPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_recordSuccessPolicyEvent
  {current : TraceResult α}
  {event : α → PolicyEvent} :
-- imply
  (current.recordSuccessPolicyEvent event).erase = current.erase := by
-- proof
  simp [TraceResult.erase]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[accesses_prependMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma accesses_prependMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.prependMemoryEvent event).trace.accesses = current.trace.accesses := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[accesses_appendMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma accesses_appendMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.appendMemoryEvent event).trace.accesses = current.trace.accesses := by
-- proof
  simp [appendMemoryEvent, AccessTrace.compose,
    AccessTrace.singletonMemoryEvent]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[pushDepths_prependMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma pushDepths_prependMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.prependMemoryEvent event).trace.pushDepths = current.trace.pushDepths := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[pushDepths_appendMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma pushDepths_appendMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.appendMemoryEvent event).trace.pushDepths = current.trace.pushDepths := by
-- proof
  simp [appendMemoryEvent, AccessTrace.compose,
    AccessTrace.singletonMemoryEvent]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[memoryEvents_prependMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma memoryEvents_prependMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.prependMemoryEvent event).trace.memoryEvents = event :: current.trace.memoryEvents := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[memoryEvents_appendMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma memoryEvents_appendMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.appendMemoryEvent event).trace.memoryEvents = current.trace.memoryEvents ++ [event] := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[memoryEvents_recordSuccessMemoryEvent_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma memoryEvents_recordSuccessMemoryEvent_of_eq_some
  {current : TraceResult α}
  {event : α → MergeMemoryEvent}
  {value : α}
-- given
  (hresult : current.result = some value) :
-- imply
  (current.recordSuccessMemoryEvent event).trace.memoryEvents = current.trace.memoryEvents ++ [event value] := by
-- proof
  simp [recordSuccessMemoryEvent, hresult]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[policyEvents_prependMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma policyEvents_prependMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.prependMemoryEvent event).trace.policyEvents = current.trace.policyEvents := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[policyEvents_appendMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma policyEvents_appendMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.appendMemoryEvent event).trace.policyEvents = current.trace.policyEvents := by
-- proof
  simp [appendMemoryEvent, AccessTrace.compose,
    AccessTrace.singletonMemoryEvent]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[policyEvents_recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma policyEvents_recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent} :
-- imply
  (current.recordSuccessMemoryEvent event).trace.policyEvents = current.trace.policyEvents := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, hresult]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[policyEvents_appendPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma policyEvents_appendPolicyEvent
  {current : TraceResult α}
  {event : PolicyEvent} :
-- imply
  (current.appendPolicyEvent event).trace.policyEvents = current.trace.policyEvents ++ [event] := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[policyEvents_recordSuccessPolicyEvent_of_eq_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma policyEvents_recordSuccessPolicyEvent_of_eq_some
  {current : TraceResult α}
  {event : α → PolicyEvent}
  {value : α}
-- given
  (hresult : current.result = some value) :
-- imply
  (current.recordSuccessPolicyEvent event).trace.policyEvents = current.trace.policyEvents ++ [event value] := by
-- proof
  simp [recordSuccessPolicyEvent, hresult]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[policyEvents_recordSuccessPolicyEvent_of_eq_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma policyEvents_recordSuccessPolicyEvent_of_eq_none
  {current : TraceResult α}
  {event : α → PolicyEvent}
-- given
  (hresult : current.result = none) :
-- imply
  (current.recordSuccessPolicyEvent event).trace.policyEvents = current.trace.policyEvents := by
-- proof
  simp [recordSuccessPolicyEvent, hresult]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[fuelExhausted_prependMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma fuelExhausted_prependMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.prependMemoryEvent event).trace.fuelExhausted = current.trace.fuelExhausted := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[fuelExhausted_appendMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma fuelExhausted_appendMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.appendMemoryEvent event).trace.fuelExhausted = current.trace.fuelExhausted := by
-- proof
  simp [appendMemoryEvent, AccessTrace.compose,
    AccessTrace.singletonMemoryEvent]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[accesses_recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma accesses_recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent} :
-- imply
  (current.recordSuccessMemoryEvent event).trace.accesses = current.trace.accesses := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, hresult]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[pushDepths_recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma pushDepths_recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent} :
-- imply
  (current.recordSuccessMemoryEvent event).trace.pushDepths = current.trace.pushDepths := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, hresult]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[fuelExhausted_recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma fuelExhausted_recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent} :
-- imply
  (current.recordSuccessMemoryEvent event).trace.fuelExhausted = current.trace.fuelExhausted := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, hresult]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[allAccessesInBounds_recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma allAccessesInBounds_recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent} :
-- imply
  (current.recordSuccessMemoryEvent event).trace.allAccessesInBounds ↔ current.trace.allAccessesInBounds := by
-- proof
  simp [AccessTrace.allAccessesInBounds]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[tempPayloadAccessesLive_recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma tempPayloadAccessesLive_recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent} :
-- imply
  (current.recordSuccessMemoryEvent event).trace.tempPayloadAccessesLive ↔ current.trace.tempPayloadAccessesLive := by
-- proof
  simp [AccessTrace.tempPayloadAccessesLive]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[stackDepthMax_prependMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma stackDepthMax_prependMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.prependMemoryEvent event).trace.stackDepthMax = current.trace.stackDepthMax := by
-- proof
  simp only [prependMemoryEvent, AccessTrace.stackDepthMax,
    AccessTrace.compose, AccessTrace.singletonMemoryEvent, List.nil_append]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[stackDepthMax_appendMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma stackDepthMax_appendMemoryEvent
  {current : TraceResult α}
  {event : MergeMemoryEvent} :
-- imply
  (current.appendMemoryEvent event).trace.stackDepthMax = current.trace.stackDepthMax := by
-- proof
  simp only [appendMemoryEvent, AccessTrace.stackDepthMax,
    AccessTrace.compose, AccessTrace.singletonMemoryEvent, List.append_nil]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[stackDepthMax_recordSuccessMemoryEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma stackDepthMax_recordSuccessMemoryEvent
  {current : TraceResult α}
  {event : α → MergeMemoryEvent} :
-- imply
  (current.recordSuccessMemoryEvent event).trace.stackDepthMax = current.trace.stackDepthMax := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessMemoryEvent, hresult]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[accesses_appendPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma accesses_appendPolicyEvent
  {current : TraceResult α}
  {event : PolicyEvent} :
-- imply
  (current.appendPolicyEvent event).trace.accesses = current.trace.accesses := by
-- proof
  simp [appendPolicyEvent, AccessTrace.compose,
    AccessTrace.singletonPolicyEvent]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[pushDepths_appendPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma pushDepths_appendPolicyEvent
  {current : TraceResult α}
  {event : PolicyEvent} :
-- imply
  (current.appendPolicyEvent event).trace.pushDepths = current.trace.pushDepths := by
-- proof
  simp [appendPolicyEvent, AccessTrace.compose,
    AccessTrace.singletonPolicyEvent]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[memoryEvents_appendPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma memoryEvents_appendPolicyEvent
  {current : TraceResult α}
  {event : PolicyEvent} :
-- imply
  (current.appendPolicyEvent event).trace.memoryEvents = current.trace.memoryEvents := by
-- proof
  simp [appendPolicyEvent, AccessTrace.compose,
    AccessTrace.singletonPolicyEvent]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[fuelExhausted_appendPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma fuelExhausted_appendPolicyEvent
  {current : TraceResult α}
  {event : PolicyEvent} :
-- imply
  (current.appendPolicyEvent event).trace.fuelExhausted = current.trace.fuelExhausted := by
-- proof
  simp [appendPolicyEvent, AccessTrace.compose,
    AccessTrace.singletonPolicyEvent]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[accesses_recordSuccessPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma accesses_recordSuccessPolicyEvent
  {current : TraceResult α}
  {event : α → PolicyEvent} :
-- imply
  (current.recordSuccessPolicyEvent event).trace.accesses = current.trace.accesses := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, hresult]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[pushDepths_recordSuccessPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma pushDepths_recordSuccessPolicyEvent
  {current : TraceResult α}
  {event : α → PolicyEvent} :
-- imply
  (current.recordSuccessPolicyEvent event).trace.pushDepths = current.trace.pushDepths := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, hresult]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[memoryEvents_recordSuccessPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma memoryEvents_recordSuccessPolicyEvent
  {current : TraceResult α}
  {event : α → PolicyEvent} :
-- imply
  (current.recordSuccessPolicyEvent event).trace.memoryEvents = current.trace.memoryEvents := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, hresult]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[fuelExhausted_recordSuccessPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma fuelExhausted_recordSuccessPolicyEvent
  {current : TraceResult α}
  {event : α → PolicyEvent} :
-- imply
  (current.recordSuccessPolicyEvent event).trace.fuelExhausted = current.trace.fuelExhausted := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, hresult]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[allAccessesInBounds_recordSuccessPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma allAccessesInBounds_recordSuccessPolicyEvent
  {current : TraceResult α}
  {event : α → PolicyEvent} :
-- imply
  (current.recordSuccessPolicyEvent event).trace.allAccessesInBounds ↔ current.trace.allAccessesInBounds := by
-- proof
  simp [AccessTrace.allAccessesInBounds]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[tempPayloadAccessesLive_recordSuccessPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma tempPayloadAccessesLive_recordSuccessPolicyEvent
  {current : TraceResult α}
  {event : α → PolicyEvent} :
-- imply
  (current.recordSuccessPolicyEvent event).trace.tempPayloadAccessesLive ↔ current.trace.tempPayloadAccessesLive := by
-- proof
  simp [AccessTrace.tempPayloadAccessesLive]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[stackDepthMax_appendPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma stackDepthMax_appendPolicyEvent
  {current : TraceResult α}
  {event : PolicyEvent} :
-- imply
  (current.appendPolicyEvent event).trace.stackDepthMax = current.trace.stackDepthMax := by
-- proof
  simp only [appendPolicyEvent, AccessTrace.stackDepthMax,
    AccessTrace.compose, AccessTrace.singletonPolicyEvent, List.append_nil]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[stackDepthMax_recordSuccessPolicyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma stackDepthMax_recordSuccessPolicyEvent
  {current : TraceResult α}
  {event : α → PolicyEvent} :
-- imply
  (current.recordSuccessPolicyEvent event).trace.stackDepthMax = current.trace.stackDepthMax := by
-- proof
  cases hresult : current.result <;>
    simp [recordSuccessPolicyEvent, hresult]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_bind
  {current : TraceResult α}
  {next : α → TraceResult β} :
-- imply
  (current.bind next).erase = current.erase.bind (fun value => (next value).erase) := by
-- proof
  cases current with
  | mk result trace =>
    cases result <;> rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[memoryEvents_bind_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma memoryEvents_bind_eq_nil
  {current : TraceResult α}
  {next : α → TraceResult β}
-- given
  (hcurrent : current.trace.memoryEvents = [])
  (hnext : ∀ value, (next value).trace.memoryEvents = []) :
-- imply
  (current.bind next).trace.memoryEvents = [] := by
-- proof
  rw [trace_bind]
  cases hresult : current.result with
  | none => exact hcurrent
  | some value =>
    simp [AccessTrace.compose, hcurrent, hnext value]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[policyEvents_bind_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma policyEvents_bind_eq_nil
  {current : TraceResult α}
  {next : α → TraceResult β}
-- given
  (hcurrent : current.trace.policyEvents = [])
  (hnext : ∀ value, (next value).trace.policyEvents = []) :
-- imply
  (current.bind next).trace.policyEvents = [] := by
-- proof
  rw [trace_bind]
  cases hresult : current.result with
  | none => exact hcurrent
  | some value =>
    simp [AccessTrace.compose, hcurrent, hnext value]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[memoryEvents_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma memoryEvents_map
  {current : TraceResult α}
  {transform : α → β} :
-- imply
  (current.map transform).trace.memoryEvents = current.trace.memoryEvents := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[policyEvents_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma policyEvents_map
  {current : TraceResult α}
  {transform : α → β} :
-- imply
  (current.map transform).trace.policyEvents = current.trace.policyEvents := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[policyEvents_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma policyEvents_bind
  {current : TraceResult α}
  {next : α → TraceResult β} :
-- imply
  (current.bind next).trace.policyEvents = match current.result with := by
-- proof
  rw [trace_bind]
  cases current.result <;> rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_markFuelExhausted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_markFuelExhausted
  {current : TraceResult α} :
-- imply
  current.markFuelExhausted.erase = current.erase := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[trace_captureAccess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma trace_captureAccess
  {kind : AccessKind}
  {region : AccessRegion}
  {index : Int}
  {extent : Nat}
  {result : Option α} :
-- imply
  (captureAccess kind region index extent result).trace = AccessTrace.singletonAccess kind region index extent := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[trace_arrayRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma trace_arrayRead
  {region : AccessRegion}
  {array : Array α}
  {index : Int} :
-- imply
  (arrayRead? region array index).trace = AccessTrace.singletonAccess .read region index array.size := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[trace_arrayWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma trace_arrayWrite
  {region : AccessRegion}
  {array : Array α}
  {index : Int}
  {value : α} :
-- imply
  (arrayWrite? region array index value).trace = AccessTrace.singletonAccess .write region index array.size := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_captureAccess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_captureAccess
  {kind : AccessKind}
  {region : AccessRegion}
  {index : Int}
  {extent : Nat}
  {result : Option α} :
-- imply
  (captureAccess kind region index extent result).erase = result := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_arrayRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_arrayRead
  {region : AccessRegion}
  {array : Array α}
  {index : Int} :
-- imply
  (arrayRead? region array index).erase = if 0 ≤ index then array[index.toNat]? else none := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_arrayWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_arrayWrite
  {region : AccessRegion}
  {array : Array α}
  {index : Int}
  {value : α} :
-- imply
  (arrayWrite? region array index value).erase = if 0 ≤ index ∧ index.toNat < array.size then some (array.setIfInBounds index.toNat value) else none := by
-- proof
  rfl
/-! ## State-derived access wrappers -/
namespace TraceResult

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[trace_tempPayloadRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma trace_tempPayloadRead
  {storage : TempStorage κ ν}
  {index : Int} :
-- imply
  (tempPayloadRead? storage index).trace = AccessTrace.singletonAccess .read (.tempPayload storage.backing) index storage.cells.size := by
-- proof
  by_cases hNonnegative : 0 ≤ index
  · cases hCell : storage.cells[index.toNat]? with
    | none =>
      simp [tempPayloadRead?, trace_bind, arrayRead?, captureAccess,
        hNonnegative, hCell]
    | some cell =>
      cases cell <;>
        simp [tempPayloadRead?, trace_bind, arrayRead?, captureAccess,
          pure, failure, hNonnegative, hCell]
  · simp [tempPayloadRead?, trace_bind, arrayRead?, captureAccess,
    hNonnegative]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[trace_tempPayloadWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma trace_tempPayloadWrite
  {storage : TempStorage κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν} :
-- imply
  (tempPayloadWrite? storage index entry).trace = AccessTrace.singletonAccess .write (.tempPayload storage.backing) index storage.cells.size := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_tempPayloadRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_tempPayloadRead
  {storage : TempStorage κ ν}
  {index : Int} :
-- imply
  (tempPayloadRead? storage index).erase = if 0 ≤ index then storage.cells[index.toNat]?.bind id else none := by
-- proof
  by_cases hNonnegative : 0 ≤ index
  · cases hCell : storage.cells[index.toNat]? with
    | none =>
      simp [tempPayloadRead?, hNonnegative, hCell]
    | some cell =>
      cases cell <;> simp [tempPayloadRead?, hNonnegative, hCell]
  · simp [tempPayloadRead?, hNonnegative]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_tempPayloadWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_tempPayloadWrite
  {storage : TempStorage κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν} :
-- imply
  (tempPayloadWrite? storage index entry).erase = if 0 ≤ index ∧ index.toNat < storage.cells.size then some { storage with cells := storage.cells.setIfInBounds index.toNat (some entry) } else none := by
-- proof
  by_cases hBounds : 0 ≤ index ∧ index.toNat < storage.cells.size <;>
    simp [tempPayloadWrite?, hBounds]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_sortSliceKeysRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_sortSliceKeysRead
  {slice : SortSlice κ ν}
  {index : Int} :
-- imply
  (sortSliceKeysRead? slice index).erase = slice.read? index := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_sortSliceValuesRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_sortSliceValuesRead
  {slice : SortSlice κ ν}
  {index : Int} :
-- imply
  (sortSliceValuesRead? slice index).erase = slice.read? index := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_sortSliceKeysWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_sortSliceKeysWrite
  {slice : SortSlice κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν} :
-- imply
  (sortSliceKeysWrite? slice index entry).erase = slice.write? index entry := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_sortSliceValuesWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_sortSliceValuesWrite
  {slice : SortSlice κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν} :
-- imply
  (sortSliceValuesWrite? slice index entry).erase = slice.write? index entry := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[trace_sortSliceKeysRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma trace_sortSliceKeysRead
  {slice : SortSlice κ ν}
  {index : Int} :
-- imply
  (sortSliceKeysRead? slice index).trace = AccessTrace.singletonAccess .read .inputKeys index slice.entries.size := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[trace_sortSliceValuesRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma trace_sortSliceValuesRead
  {slice : SortSlice κ ν}
  {index : Int} :
-- imply
  (sortSliceValuesRead? slice index).trace = AccessTrace.singletonAccess .read .synchronizedValues index slice.entries.size := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[trace_sortSliceKeysWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma trace_sortSliceKeysWrite
  {slice : SortSlice κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν} :
-- imply
  (sortSliceKeysWrite? slice index entry).trace = AccessTrace.singletonAccess .write .inputKeys index slice.entries.size := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[trace_sortSliceValuesWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma trace_sortSliceValuesWrite
  {slice : SortSlice κ ν}
  {index : Int}
  {entry : SortSliceEntry κ ν} :
-- imply
  (sortSliceValuesWrite? slice index entry).trace = AccessTrace.singletonAccess .write .synchronizedValues index slice.entries.size := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_pendingRunRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_pendingRunRead
  {state : MergeState κ ν}
  {index : Int} :
-- imply
  (pendingRunRead? state index).erase = if 0 ≤ index then state.pending[index.toNat]? else none := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_pendingRunWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_pendingRunWrite
  {state : MergeState κ ν}
  {index : Int}
  {run : PendingRun} :
-- imply
  (pendingRunWrite? state index run).erase = if 0 ≤ index ∧ index.toNat < state.pending.size then some { state with pending := state.pending.setIfInBounds index.toNat run } else none := by
-- proof
  by_cases hBounds : 0 ≤ index ∧ index.toNat < state.pending.size <;>
    simp [pendingRunWrite?, hBounds]

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[erase_pendingRunPowerWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_pendingRunPowerWrite
  {state : MergeState κ ν}
  {index : Int}
  {power : Nat} :
-- imply
  (pendingRunPowerWrite? state index power).erase = if 0 ≤ index then state.pending[index.toNat]?.map fun top => { state with pending := state.pending.setIfInBounds index.toNat ({ top with power := some power } : PendingRun) } else none := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[trace_pendingRunRead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma trace_pendingRunRead
  {state : MergeState κ ν}
  {index : Int} :
-- imply
  (pendingRunRead? state index).trace = AccessTrace.singletonAccess .read .pendingRuns index state.pending.size := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[trace_pendingRunWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma trace_pendingRunWrite
  {state : MergeState κ ν}
  {index : Int}
  {run : PendingRun} :
-- imply
  (pendingRunWrite? state index run).trace = AccessTrace.singletonAccess .write .pendingRuns index state.pending.size := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort.TraceResult

/--
[trace_pendingRunPowerWrite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma trace_pendingRunPowerWrite
  {state : MergeState κ ν}
  {index : Int}
  {power : Nat} :
-- imply
  (pendingRunPowerWrite? state index power).trace = AccessTrace.singletonAccess .write .pendingRuns index state.pending.size := by
-- proof
  rfl

end CPythonListsort.TraceResult

namespace CPythonListsort

/--
[erase_pushPendingRunTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_pushPendingRunTraced
  {state : MergeState κ ν}
  {run : PendingRun} :
-- imply
  (pushPendingRunTraced state run).erase = some { state with pending := state.pending.push run } := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[trace_pushPendingRunTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma trace_pushPendingRunTraced
  {state : MergeState κ ν}
  {run : PendingRun} :
-- imply
  (pushPendingRunTraced state run).trace = AccessTrace.singletonPushDepth (state.pending.size + 1) := by
-- proof
  simp [pushPendingRunTraced, AccessTrace.singletonPushDepth]

end CPythonListsort

namespace CPythonListsort

/--
[erase_pushFormedRunTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma erase_pushFormedRunTraced
  {state : MergeState κ ν}
  {run : PendingRun}
  {naturalLength target remainingBefore : Nat} :
-- imply
  (pushFormedRunTraced state run naturalLength target remainingBefore).erase = some { state with pending := state.pending.push run } := by
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[trace_pushFormedRunTraced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma trace_pushFormedRunTraced
  {state : MergeState κ ν}
  {run : PendingRun}
  {naturalLength target remainingBefore : Nat} :
-- imply
  (pushFormedRunTraced state run naturalLength target remainingBefore).trace = AccessTrace.singletonFormedRun { run := RunSpan.ofPendingRun run depthAfter := state.pending.size + 1 naturalLength := naturalLength target := target remainingBefore := remainingBefore } := by
-- proof
  simp [pushFormedRunTraced, AccessTrace.singletonFormedRun]

end CPythonListsort

namespace CPythonListsort

/--
[pushFormedRunTraced_legacyProjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma pushFormedRunTraced_legacyProjection
  {state : MergeState κ ν}
  {run : PendingRun}
  {naturalLength target remainingBefore : Nat} :
-- imply
  (pushFormedRunTraced state run naturalLength target remainingBefore).erase = (pushPendingRunTraced state run).erase ∧ (pushFormedRunTraced state run naturalLength target remainingBefore).trace.accesses = (pushPendingRunTraced state run).trace.accesses ∧ (pushFormedRunTraced state run naturalLength target remainingBefore).trace.pushDepths = (pushPendingRunTraced state run).trace.pushDepths ∧ (pushFormedRunTraced state run naturalLength target remainingBefore).trace.memoryEvents = (pushPendingRunTraced state run).trace.memoryEvents ∧ (pushFormedRunTraced state run naturalLength target remainingBefore).trace.fuelExhausted = (pushPendingRunTraced state run).trace.fuelExhausted := by
-- proof
  refine ⟨rfl, ?_⟩
  simp [pushFormedRunTraced, pushPendingRunTraced,
    AccessTrace.singletonFormedRun, AccessTrace.singletonPushDepth]

end CPythonListsort

namespace CPythonListsort

/--
[pushFormedRunTraced_policyEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma pushFormedRunTraced_policyEvent
  {state : MergeState κ ν}
  {run : PendingRun}
  {naturalLength target remainingBefore : Nat} :
-- imply
  (pushFormedRunTraced state run naturalLength target remainingBefore).trace.policyEvents = [.formed { run := RunSpan.ofPendingRun run depthAfter := state.pending.size + 1 naturalLength := naturalLength target := target remainingBefore := remainingBefore }] ∧ (pushFormedRunTraced state run naturalLength target remainingBefore).trace.pushDepths = [state.pending.size + 1] := by
-- proof
  simp [trace_pushFormedRunTraced, AccessTrace.singletonFormedRun]

end CPythonListsort

namespace CPythonListsort

/--
[forcedPushAtCapacity_records65](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma forcedPushAtCapacity_records65
-- imply
  accessTraceForcedPush.result.map Array.size = some 65 ∧ accessTraceForcedPush.trace.pushDepths = [65] ∧ accessTraceForcedPush.trace.stackDepthMax = 65 := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[pushPendingRunTraced_at_capacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma pushPendingRunTraced_at_capacity
  {state : MergeState κ ν}
  {run : PendingRun}
-- given
  (hDepth : state.pending.size = MAX_MERGE_PENDING) :
-- imply
  (pushPendingRunTraced state run).result.map (fun pushed => pushed.pending.size) = some 65 ∧ (pushPendingRunTraced state run).trace.pushDepths = [65] ∧ (pushPendingRunTraced state run).trace.stackDepthMax = 65 := by
-- proof
  simp [pushPendingRunTraced, hDepth, MAX_MERGE_PENDING,
    AccessTrace.singletonPushDepth, AccessTrace.stackDepthMax]

end CPythonListsort

namespace CPythonListsort

/--
[rejectedReleasedTempRead_is_observable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma rejectedReleasedTempRead_is_observable
-- imply
  rejectedReleasedTempRead.result = none ∧ rejectedReleasedTempRead.trace.accesses = [{ kind := .read, region := .tempPayload .released, index := 0, extent := 0 }] ∧ ¬rejectedReleasedTempRead.trace.allAccessesInBounds ∧ ¬rejectedReleasedTempRead.trace.tempPayloadAccessesLive := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[rejectedUninitializedTempRead_is_observable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma rejectedUninitializedTempRead_is_observable
-- imply
  rejectedUninitializedTempRead.result = none ∧ rejectedUninitializedTempRead.trace.accesses = [{ kind := .read, region := .tempPayload .inline, index := 0, extent := 1 }] ∧ rejectedUninitializedTempRead.trace.allAccessesInBounds ∧ rejectedUninitializedTempRead.trace.tempPayloadAccessesLive := by
-- proof
  decide

end CPythonListsort

namespace CPythonListsort

/--
[localTraceComposition_preserves_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
lemma localTraceComposition_preserves_order
-- imply
  orderedAccessRegression.trace.accesses = [{ kind := .read, region := .inputKeys, index := 1, extent := 2 }, { kind := .write, region := .synchronizedValues, index := 0, extent := 2 }] ∧ orderedAccessRegression.trace.allAccessesInBounds ∧ orderedAccessRegression.trace.tempPayloadAccessesLive := by
-- proof
  decide

end CPythonListsort

/--
[allAccessesInBounds_compose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
private lemma allAccessesInBounds_compose_eq
  {earlier later : AccessTrace} :
-- imply
  (compose earlier later).allAccessesInBounds ↔ earlier.allAccessesInBounds ∧ later.allAccessesInBounds := by
-- proof
  apply CPythonListsort.AccessTrace.allAccessesInBounds_compose earlier later

/--
[tempPayloadAccessesLive_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
private lemma tempPayloadAccessesLive_empty_eq :
-- imply
  empty.tempPayloadAccessesLive := by
-- proof
  apply CPythonListsort.AccessTrace.tempPayloadAccessesLive_empty

/--
[tempPayloadAccessesLive_compose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
private lemma tempPayloadAccessesLive_compose_eq
  {earlier later : AccessTrace} :
-- imply
  (compose earlier later).tempPayloadAccessesLive ↔ earlier.tempPayloadAccessesLive ∧ later.tempPayloadAccessesLive := by
-- proof
  apply CPythonListsort.AccessTrace.tempPayloadAccessesLive_compose earlier later

/--
[trace_bind](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/AccessTrace.lean)
-/
@[path]
private lemma trace_bind_eq
  {current : TraceResult α}
  {next : α → TraceResult β} :
-- imply
  (current.bind next).trace = match current.result with := by
-- proof
  apply CPythonListsort.TraceResult.trace_bind current next


-- created on 2026-10-23
