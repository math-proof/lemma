import Mathlib
import sympy.Basic
import Theorem.CPythonListsort.Code.Transcription.MergeForceCollapse


namespace CPythonListsort

/--
[PendingRunsCover.singleton_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/MergeForceCollapsePreservation.lean)
-/
@[path]
lemma PendingRunsCover.singleton_geometry
  {κ : Type u}
  {ν : Type v}
  {cursor limit : Nat}
  {run : PendingRun}
-- given
  (hcover : PendingRunsCover cursor limit [run]) :
-- imply
  run.base = cursor ∧ run.endIndex = limit := by
-- proof
  simp only [PendingRunsCover] at hcover
  exact ⟨hcover.1, hcover.2.2.2.2⟩

end CPythonListsort

namespace CPythonListsort

variable {κ : Type u} {ν : Type v}
/--
[mergeForceCollapseLoop_preserves_pendingLayout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/MergeForceCollapsePreservation.lean)
-/
@[path]
successful recursive step preserves the structural frame and pending layout;
an initially nonempty stack therefore stops with exactly one run.
The lemma makes no claim that a successful, non-fuel-exhausted result
exists. -/
private theorem mergeForceCollapseLoop_preserves_pendingLayout
  (fuel : Nat) (state : MergeState κ ν) (scanned : Nat)
  (result : MergeForceCollapseResult κ ν)
  (hnonempty : state.pending.toList ≠ [])
  (hlayout : PendingLayout state scanned)
  (hloop : mergeForceCollapseLoop? fuel state = some result)
  (hcode : result.returnCode = 0)
  (hfuel : result.fuelExhausted = false) :
  result.state.listlen = state.listlen ∧
    result.state.basekeys = state.basekeys ∧
    result.state.data.entries.size = state.data.entries.size ∧
    PendingLayout result.state scanned ∧
    ∃ run, result.state.pending.toList = [run] := by
  induction fuel generalizing state result with
  | zero =>
    simp only [mergeForceCollapseLoop?] at hloop
    by_cases hsmall : state.pending.size ≤ 1
    · rw [if_pos hsmall] at hloop
      injection hloop with hresult
      subst result
      have hlengthLe : state.pending.toList.length ≤ 1 := by
        simpa using hsmall
      have hlengthPositive : 0 < state.pending.toList.length :=
        List.length_pos_of_ne_nil hnonempty
      have hlength : state.pending.toList.length = 1 := by omega
      obtain ⟨run, hruns⟩ := List.length_eq_one_iff.mp hlength
      exact ⟨rfl, rfl, rfl, hlayout, run, hruns⟩
    · rw [if_neg hsmall] at hloop
      injection hloop with hresult
      subst result
      change true = false at hfuel
      contradiction
  | succ remaining ih =>
    simp only [mergeForceCollapseLoop?] at hloop
    by_cases hmany : 1 < state.pending.size
    · rw [if_pos hmany] at hloop
      cases hindex : forceCollapseIndex? state with
      | none => simp [hindex] at hloop
      | some i =>
        simp only [hindex] at hloop
        cases hmerge : mergeAt? state i with
        | none => simp [hmerge] at hloop
        | some merged =>
          simp only [hmerge] at hloop
          by_cases hmergeSuccess :
            merged.returnCode = 0 ∧ !merged.fuelExhausted
          · rw [if_pos hmergeSuccess] at hloop
            rcases mergeAt_preserves_pendingLayout state scanned i
              merged hlayout hmerge with
              ⟨before, left, right, after, _, _, hmergedPending,
                _, _, _, _, _, _, hmergedLayout⟩
            rcases mergeAt_pending_frame_of_eq_some state i merged
              hmerge with
              ⟨_, _, _, _, hmergedListlen, hmergedBasekeys,
                hmergedDataSize, _⟩
            have hmergedNonempty :
              merged.state.pending.toList ≠ [] := by
              rw [hmergedPending]
              simp
            rcases ih merged.state result hmergedNonempty hmergedLayout
              hloop hcode hfuel with
              ⟨hresultListlen, hresultBasekeys, hresultDataSize,
                hresultLayout, run, hresultPending⟩
            exact
              ⟨hresultListlen.trans hmergedListlen,
                hresultBasekeys.trans hmergedBasekeys,
                hresultDataSize.trans hmergedDataSize,
                hresultLayout, run, hresultPending⟩
          · rw [if_neg hmergeSuccess] at hloop
            injection hloop with hresult
            subst result
            change merged.returnCode = 0 at hcode
            change merged.fuelExhausted = false at hfuel
            exfalso
            apply hmergeSuccess
            exact ⟨hcode, by simp [hfuel]⟩
    · rw [if_neg hmany] at hloop
      injection hloop with hresult
      subst result
      have hsmall : state.pending.size ≤ 1 := by omega
      have hlengthLe : state.pending.toList.length ≤ 1 := by
        simpa using hsmall
      have hlengthPositive : 0 < state.pending.toList.length :=
        List.length_pos_of_ne_nil hnonempty
      have hlength : state.pending.toList.length = 1 := by omega
      obtain ⟨run, hruns⟩ := List.length_eq_one_iff.mp hlength
      exact ⟨rfl, rfl, rfl, hlayout, run, hruns⟩

end CPythonListsort

namespace CPythonListsort

/--
[mergeForceCollapse_preserves_pendingLayout](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/MergeForceCollapsePreservation.lean)
-/
@[path]
lemma mergeForceCollapse_preserves_pendingLayout
  {κ : Type u}
  {ν : Type v}
  {state : MergeState κ ν}
  {scanned : Nat}
  {result : MergeForceCollapseResult κ ν}
-- given
  (hnonempty : state.pending.toList ≠ [])
  (hlayout : PendingLayout state scanned)
  (hcollapse : mergeForceCollapse? state = some result)
  (hcode : result.returnCode = 0)
  (hfuel : result.fuelExhausted = false) :
-- imply
  result.state.listlen = state.listlen ∧ result.state.basekeys = state.basekeys ∧ result.state.data.entries.size = state.data.entries.size ∧ PendingLayout result.state scanned ∧ ∃ run, result.state.pending.toList = [run] ∧ run.base = state.basekeys ∧ run.endIndex = state.basekeys + scanned := by
-- proof
  unfold mergeForceCollapse? at hcollapse
  rcases mergeForceCollapseLoop_preserves_pendingLayout
    state.pending.size state scanned result hnonempty hlayout hcollapse
    hcode hfuel with
    ⟨hlistlen, hbasekeys, hdataSize, hresultLayout, run, hpending⟩
  have hcover : PendingRunsCover result.state.basekeys
    (result.state.basekeys + scanned) [run] := by
    simpa [hpending] using hresultLayout.2.2.2
  have hgeometry := hcover.singleton_geometry
  refine
    ⟨hlistlen, hbasekeys, hdataSize, hresultLayout, run, hpending, ?_, ?_⟩
  · exact hgeometry.1.trans hbasekeys
  · rw [hgeometry.2, hbasekeys]

end CPythonListsort


-- created on 2026-10-23
