import Mathlib
import sympy.Basic
import Def.CPythonListsort.Code.Policy.StackPowers.Part2
open CPythonListsort


namespace CPythonListsort

/--
[increasingPendingPowers_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma increasingPendingPowers_nil
-- imply
  IncreasingPendingPowers [] :=
-- proof
⟨[], rfl, by simp, by simp⟩

end CPythonListsort

namespace CPythonListsort

/--
[poweredPrefix_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma poweredPrefix_singleton
  {state : MergeState κ ν}
  {run : PendingRun} :
-- imply
  PoweredPrefix { state with pending := #[run] } := by
-- proof
  right
  exact ⟨[], run, by simp, increasingPendingPowers_nil, by simp⟩

end CPythonListsort

/--
[exactBoundaryPowers_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma exactBoundaryPowers_nil
  {basekeys : Nat}
  {listlen : PySSize} :
-- imply
  ExactBoundaryPowers basekeys listlen [] := by
-- proof
  simp [ExactBoundaryPowers]


namespace CPythonListsort

/--
[exactBoundaryPowers_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma exactBoundaryPowers_singleton
  {basekeys : Nat}
  {listlen : PySSize}
  {run : PendingRun} :
-- imply
  ExactBoundaryPowers basekeys listlen [run] := by
-- proof
  simp [ExactBoundaryPowers]

end CPythonListsort

namespace CPythonListsort

/--
[ExactBoundaryPowers.head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma ExactBoundaryPowers.head
  {basekeys : Nat}
  {listlen : PySSize}
  {left right : PendingRun}
  {rest : List PendingRun}
-- given
  (h : ExactBoundaryPowers basekeys listlen (left :: right :: rest)) :
-- imply
  left.power = some (pendingBoundaryPower basekeys listlen left right) :=
-- proof
h.1

end CPythonListsort

namespace CPythonListsort

/--
[ExactBoundaryPowers.tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma ExactBoundaryPowers.tail
  {basekeys : Nat}
  {listlen : PySSize}
  {head : PendingRun}
  {tail : List PendingRun}
-- given
  (h : ExactBoundaryPowers basekeys listlen (head :: tail)) :
-- imply
  ExactBoundaryPowers basekeys listlen tail := by
-- proof
  cases tail with
  | nil => simp
  | cons next rest => exact h.2

end CPythonListsort

namespace CPythonListsort

/--
[ExactBoundaryPowers.pair_of_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma ExactBoundaryPowers.pair_of_append
  {basekeys : Nat}
  {listlen : PySSize}
  {before after : List PendingRun}
  {left right : PendingRun}
-- given
  (h : ExactBoundaryPowers basekeys listlen (before ++ left :: right :: after)) :
-- imply
  left.power = some (pendingBoundaryPower basekeys listlen left right) := by
-- proof
  induction before with
  | nil => exact h.head
  | cons head before ih =>
    exact ih h.tail

end CPythonListsort

namespace CPythonListsort

/--
[increasingPendingPowers_singleton_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma increasingPendingPowers_singleton_iff
  {run : PendingRun} :
-- imply
  IncreasingPendingPowers [run] ↔ ∃ power, run.power = some power ∧ 1 ≤ power ∧ power ≤ 60 := by
-- proof
  constructor
  · rintro ⟨powers, hpowers, hrange, _⟩
    cases powers with
    | nil => simp at hpowers
    | cons power rest =>
      simp only [List.map_cons, List.cons.injEq] at hpowers
      obtain ⟨hrun, hrest⟩ := hpowers
      have : rest = [] := by
        simpa using hrest
      subst rest
      exact ⟨power, hrun, (hrange power (by simp)).1,
        (hrange power (by simp)).2⟩
  · rintro ⟨power, hpower, hlower, hupper⟩
    refine ⟨[power], by simp [hpower], ?_, by simp⟩
    intro candidate hcandidate
    simp only [List.mem_singleton] at hcandidate
    subst candidate
    exact ⟨hlower, hupper⟩

end CPythonListsort

namespace CPythonListsort

/--
[IncreasingPendingPowers.run_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma IncreasingPendingPowers.run_power
  {runs : List PendingRun}
  {run : PendingRun}
-- given
  (h : IncreasingPendingPowers runs)
  (hrun : run ∈ runs) :
-- imply
  ∃ power, run.power = some power ∧ 1 ≤ power ∧ power ≤ 60 := by
-- proof
  obtain ⟨powers, hpowers, hrange, _⟩ := h
  have hmapped : run.power ∈ powers.map some := by
    rw [← hpowers]
    exact List.mem_map.mpr ⟨run, hrun, rfl⟩
  obtain ⟨power, hpowerMem, hpower⟩ := List.mem_map.mp hmapped
  exact ⟨power, hpower.symm, (hrange power hpowerMem).1,
    (hrange power hpowerMem).2⟩

end CPythonListsort

namespace CPythonListsort

/--
[IncreasingPendingPowers.length_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma IncreasingPendingPowers.length_eq
  {runs : List PendingRun}
-- given
  (h : IncreasingPendingPowers runs) :
-- imply
  ∃ powers : List Nat, powers.length = runs.length ∧ (∀ power ∈ powers, 1 ≤ power ∧ power ≤ 60) ∧ powers.Pairwise (· < ·) := by
-- proof
  obtain ⟨powers, hpowers, hrange, hstrict⟩ := h
  refine ⟨powers, ?_, hrange, hstrict⟩
  have := congrArg List.length hpowers
  simpa using this.symm

end CPythonListsort

namespace CPythonListsort

/--
[poweredPrefix_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma poweredPrefix_empty
  {state : MergeState κ ν} :
-- imply
  PoweredPrefix { state with pending := #[] } := by
-- proof
  simp [PoweredPrefix]

end CPythonListsort

namespace CPythonListsort

/--
[PoweredPrefix.split_of_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma PoweredPrefix.split_of_nonempty
  {state : MergeState κ ν}
-- given
  (h : PoweredPrefix state)
  (hne : state.pending.toList ≠ []) :
-- imply
  ∃ olderRuns newest, state.pending.toList = olderRuns ++ [newest] ∧ IncreasingPendingPowers olderRuns ∧ ExactBoundaryPowers state.basekeys state.listlen state.pending.toList :=
-- proof
h.resolve_left hne

end CPythonListsort

namespace CPythonListsort

/--
[PoweredPrefix.exact_boundary_powers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma PoweredPrefix.exact_boundary_powers
  {state : MergeState κ ν}
-- given
  (h : PoweredPrefix state) :
-- imply
  ExactBoundaryPowers state.basekeys state.listlen state.pending.toList := by
-- proof
  obtain hempty | ⟨_, _, _, _, hexact⟩ := h
  · simp [hempty]
  · exact hexact

end CPythonListsort

namespace CPythonListsort

/--
[PoweredPrefix.boundary_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma PoweredPrefix.boundary_power
  {state : MergeState κ ν}
  {before after : List PendingRun}
  {left right : PendingRun}
-- given
  (h : PoweredPrefix state)
  (hsplit : state.pending.toList = before ++ left :: right :: after) :
-- imply
  left.power = some (pendingBoundaryPower state.basekeys state.listlen left right) := by
-- proof
  apply ExactBoundaryPowers.pair_of_append
  rwa [← hsplit]

end CPythonListsort

namespace CPythonListsort

/--
[PoweredPrefix.run_power_of_mem_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma PoweredPrefix.run_power_of_mem_prefix
  {state : MergeState κ ν}
  {olderRuns : List PendingRun}
  {newest run : PendingRun}
-- given
  (h : PoweredPrefix state)
  (hsplit : state.pending.toList = olderRuns ++ [newest])
  (hrun : run ∈ olderRuns) :
-- imply
  ∃ power, run.power = some power ∧ 1 ≤ power ∧ power ≤ 60 := by
-- proof
  obtain hempty | := h
    ⟨actualOlderRuns, actualNewest, hactual, hpowers, _hexact⟩
  · rw [hempty] at hsplit
    simp at hsplit
  · have heq : olderRuns ++ [newest] = actualOlderRuns ++ [actualNewest] :=
    hsplit.symm.trans hactual
    have hlength : olderRuns.length = actualOlderRuns.length := by
      have hlengthWithTop := congrArg List.length heq
      simp only [List.length_append, List.length_singleton] at hlengthWithTop
      exact Nat.add_right_cancel hlengthWithTop
    have hparts := List.append_inj heq hlength
    rw [hparts.1] at hrun
    exact hpowers.run_power hrun

end CPythonListsort

namespace CPythonListsort

/--
[ReadyToPush.layout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma ReadyToPush.layout
  {state : MergeState κ ν}
  {scanned : Nat}
  {newRun : PendingRun}
-- given
  (h : ReadyToPush state scanned newRun) :
-- imply
  PendingLayout state scanned :=
-- proof
  h.1

end CPythonListsort

namespace CPythonListsort

/--
[ReadyToPush.current_powers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma ReadyToPush.current_powers
  {state : MergeState κ ν}
  {scanned : Nat}
  {newRun : PendingRun}
-- given
  (h : ReadyToPush state scanned newRun) :
-- imply
  IncreasingPendingPowers state.pending.toList :=
-- proof
  h.2.1

end CPythonListsort

namespace CPythonListsort

/--
[ReadyToPush.virtual_boundary_powers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma ReadyToPush.virtual_boundary_powers
  {state : MergeState κ ν}
  {scanned : Nat}
  {newRun : PendingRun}
-- given
  (h : ReadyToPush state scanned newRun) :
-- imply
  ExactBoundaryPowers state.basekeys state.listlen (state.pending.toList ++ [newRun]) :=
-- proof
  h.2.2.1

end CPythonListsort

namespace CPythonListsort

/--
[ReadyToPush.new_run_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma ReadyToPush.new_run_adjacent
  {state : MergeState κ ν}
  {scanned : Nat}
  {newRun : PendingRun}
-- given
  (h : ReadyToPush state scanned newRun) :
-- imply
  newRun.base = state.basekeys + scanned :=
-- proof
  h.2.2.2.1

end CPythonListsort

namespace CPythonListsort

/--
[ReadyToPush.new_run_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma ReadyToPush.new_run_nonempty
  {state : MergeState κ ν}
  {scanned : Nat}
  {newRun : PendingRun}
-- given
  (h : ReadyToPush state scanned newRun) :
-- imply
  newRun.len.Nonnegative ∧ 0 < newRun.len.toNat :=
-- proof
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩

end CPythonListsort

namespace CPythonListsort

/--
[ReadyToPush.new_run_within_input](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma ReadyToPush.new_run_within_input
  {state : MergeState κ ν}
  {scanned : Nat}
  {newRun : PendingRun}
-- given
  (h : ReadyToPush state scanned newRun) :
-- imply
  scanned + newRun.len.toNat ≤ state.listlen.toNat :=
-- proof
  h.2.2.2.2.2.2.1

end CPythonListsort

namespace CPythonListsort

/--
[ReadyToPush.new_run_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma ReadyToPush.new_run_outside
  {state : MergeState κ ν}
  {scanned : Nat}
  {newRun : PendingRun}
-- given
  (h : ReadyToPush state scanned newRun) :
-- imply
  newRun ∉ state.pending.toList :=
-- proof
  h.2.2.2.2.2.2.2

end CPythonListsort

namespace CPythonListsort

/--
[mislabeledBoundary_true_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
boundary power `1`, not the stored label `2`.  This uses ordinary kernel
reduction rather than an external evaluator. -/
private lemma mislabeledBoundary_true_power :
  pendingBoundaryPower 0 (3 : PySSize) mislabeledOlder unlabeledNewest = 1 := by
  decide

end CPythonListsort

namespace CPythonListsort

/--
[fabricatedTwoRunStack_not_powered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean)
-/
@[path]
lemma fabricatedTwoRunStack_not_powered
  {state : MergeState κ ν} :
-- imply
  ¬PoweredPrefix { state with listlen := 3 basekeys := 0 pending := #[{ base := 0, len := 1, power := some 2 }, { base := 1, len := 1, power := none }] } := by
-- proof
  change ¬PoweredPrefix
    { state with
      listlen := 3
      basekeys := 0
      pending := #[mislabeledOlder, unlabeledNewest] }
  intro h
  have hexact := h.exact_boundary_powers
  have hlabel := hexact.head
  rw [mislabeledBoundary_true_power] at hlabel
  simp [mislabeledOlder] at hlabel

end CPythonListsort


-- created on 2026-10-23
