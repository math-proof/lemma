import Mathlib
import sympy.Basic
import sympy.atlas.CPythonListsort.Code.Equivalence.PowerloopResults
import sympy.atlas.CPythonListsort.Code.Policy.StackPowers
import sympy.atlas.CPythonListsort.Code.Transcription.ListSortImpl


namespace CPythonListsort

/--
[increasingPowers_length_le_powerBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackDepth.lean)
-/
@[path]
lemma increasingPowers_length_le_powerBound
  {powers : List Nat}
-- given
  (hrange : ∀ power ∈ powers, 1 ≤ power ∧ power ≤ POWER_BOUND)
  (hstrict : powers.Pairwise (· < ·)) :
-- imply
  powers.length ≤ POWER_BOUND := by
-- proof
  have hsubset : powers.toFinset ⊆ Finset.Icc 1 POWER_BOUND := by
    intro power hpower
    rw [List.mem_toFinset] at hpower
    exact Finset.mem_Icc.mpr (hrange power hpower)
  have hcard := Finset.card_le_card hsubset
  rw [List.toFinset_card_of_nodup hstrict.nodup] at hcard
  simpa [POWER_BOUND] using hcard

end CPythonListsort

namespace CPythonListsort

/--
[IncreasingPendingPowers.length_le_powerBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackDepth.lean)
-/
@[path]
lemma IncreasingPendingPowers.length_le_powerBound
  {runs : List PendingRun}
-- given
  (h : IncreasingPendingPowers runs) :
-- imply
  runs.length ≤ POWER_BOUND := by
-- proof
  obtain ⟨powers, hlength, hrange, hstrict⟩ := h.length_eq
  have hrange' : ∀ power ∈ powers, 1 ≤ power ∧ power ≤ POWER_BOUND := by
    simpa [POWER_BOUND] using hrange
  rw [← hlength]
  exact increasingPowers_length_le_powerBound hrange' hstrict

end CPythonListsort

namespace CPythonListsort

/--
[ReadyToPush.current_depth_le_sixty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackDepth.lean)
-/
@[path]
lemma ReadyToPush.current_depth_le_sixty
  {state : MergeState κ ν}
  {scanned : Nat}
  {newRun : PendingRun}
-- given
  (hready : ReadyToPush state scanned newRun) :
-- imply
  state.pending.size ≤ 60 := by
-- proof
  have hbound := hready.current_powers.length_le_powerBound
  simpa [POWER_BOUND] using hbound

end CPythonListsort

namespace CPythonListsort

/--
[readyToPush_stack_depth_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackDepth.lean)
-/
@[path]
lemma readyToPush_stack_depth_bound
  {state : MergeState κ ν}
  {scanned : Nat}
  {newRun : PendingRun}
-- given
  (hready : ReadyToPush state scanned newRun) :
-- imply
  state.pending.size ≤ 60 ∧ (pushPendingRun state newRun).pending.size = state.pending.size + 1 ∧ (pushPendingRun state newRun).pending.size ≤ 61 ∧ (pushPendingRun state newRun).pending.size < MAX_MERGE_PENDING := by
-- proof
  have hcurrent : state.pending.size ≤ 60 :=
    hready.current_depth_le_sixty
  have hexact := pushPendingRun_size state newRun
  refine ⟨hcurrent, hexact, ?_, ?_⟩
  · omega
  · rw [hexact]
    have hcapacity := powerBound_relation.2
    omega

end CPythonListsort


-- created on 2026-10-23
