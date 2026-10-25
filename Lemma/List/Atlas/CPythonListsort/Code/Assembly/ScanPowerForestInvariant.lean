import Mathlib
import sympy.Basic
import Structure.CPythonListsort.Code.Assembly.ScanPowerForestInvariant.Part2
open CPythonListsort CPythonListsort.ScanPowerForestInv


namespace CPythonListsort.ScanPowerForestInv

/--
[spans_eq_of_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ScanPowerForestInvariant.lean)
-/
@[path]
private lemma spans_eq_of_aligned
  {input : RunSpan} {forest : List SpannedMergeTree}
  {runs : List PendingRun}
  (h : List.Forall₂ (RunTreeAligned input) forest runs) :
  forest.map SpannedMergeTree.span = runs.map RunSpan.ofPendingRun := by
  induction h with
  | nil => rfl
  | cons haligned _ ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨haligned.span_eq, ih⟩

end CPythonListsort.ScanPowerForestInv

namespace CPythonListsort.ScanPowerForestInv

/--
[spans_eq_pending](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ScanPowerForestInvariant.lean)
-/
@[path]
lemma spans_eq_pending
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {state : MergeState κ ν}
-- given
  (h : ScanPowerForestInv input forest state) :
-- imply
  forest.map SpannedMergeTree.span = state.pending.toList.map RunSpan.ofPendingRun :=
-- proof
spans_eq_of_aligned h.aligned

end CPythonListsort.ScanPowerForestInv

namespace CPythonListsort.ScanPowerForestInv

/--
[length_eq_pending](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ScanPowerForestInvariant.lean)
-/
@[path]
lemma length_eq_pending
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {state : MergeState κ ν}
-- given
  (h : ScanPowerForestInv input forest state) :
-- imply
  forest.length = state.pending.size := by
-- proof
  simpa using h.aligned.length_eq

end CPythonListsort.ScanPowerForestInv

namespace CPythonListsort.ScanPowerForestInv

/--
[tree_valid_of_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ScanPowerForestInvariant.lean)
-/
@[path]
private lemma tree_valid_of_aligned
  {input : RunSpan} {forest : List SpannedMergeTree}
  {runs : List PendingRun}
  (h : List.Forall₂ (RunTreeAligned input) forest runs)
  {entry : SpannedMergeTree} (hentry : entry ∈ forest) :
  entry.Valid ∧
    entry.tree.PowerValid input.base (BitVec.ofNat 64 input.len)
      entry.span.base := by
  induction h with
  | nil => simp at hentry
  | @cons head run forest runs hhead htail ih =>
    simp only [List.mem_cons] at hentry
    obtain rfl | hentry := hentry
    · exact ⟨hhead.valid, hhead.powerValid⟩
    · exact ih hentry

end CPythonListsort.ScanPowerForestInv

namespace CPythonListsort.ScanPowerForestInv

/--
[tree_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ScanPowerForestInvariant.lean)
-/
@[path]
lemma tree_valid
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {state : MergeState κ ν}
  {entry : SpannedMergeTree}
-- given
  (h : ScanPowerForestInv input forest state)
  (hentry : entry ∈ forest) :
-- imply
  entry.Valid ∧ entry.tree.PowerValid input.base (BitVec.ofNat 64 input.len) entry.span.base :=
-- proof
tree_valid_of_aligned h.aligned hentry

end CPythonListsort.ScanPowerForestInv

namespace CPythonListsort.ScanPowerForestInv

/--
[openSpanChain_of_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ScanPowerForestInvariant.lean)
-/
@[path]
private lemma openSpanChain_of_cover
  {input : RunSpan} {cursor limit : Nat}
  {forest : List SpannedMergeTree} {runs : List PendingRun}
  (hcursor : input.base ≤ cursor)
  (hlimit : limit = input.endIndex)
  (hcover : PendingRunsCover cursor limit runs)
  (haligned : List.Forall₂ (RunTreeAligned input) forest runs) :
  OpenSpanChain input cursor forest := by
  induction haligned generalizing cursor with
  | nil =>
    exact .empty (by simpa [PendingRunsCover, hlimit] using hcover)
  | @cons entry run forest runs hentry _ ih =>
    rcases hcover with
      ⟨hbase, hnonnegative, hpositive, hwithin, htail⟩
    have hentryBase : entry.span.base = cursor := by
      rw [hentry.span_eq]
      simpa [RunSpan.ofPendingRun] using hbase
    have hentryValid : entry.span.ValidWithin input := by
      rw [hentry.span_eq]
      refine ⟨?_, ?_, ?_⟩
      · simpa [RunSpan.ofPendingRun, hbase] using hcursor
      · simpa [RunSpan.ofPendingRun, RunSpan.endIndex,
        PendingRun.endIndex, hlimit] using hwithin
      · simpa [RunSpan.ofPendingRun] using hpositive
    apply OpenSpanChain.cons entry forest hentryBase hentryValid
    have hend : entry.span.endIndex = run.endIndex := by
      simp [hentry.span_eq, RunSpan.ofPendingRun, RunSpan.endIndex,
        PendingRun.endIndex]
    rw [hend]
    apply ih
    · simp only [PendingRun.endIndex]
      omega
    · exact htail

end CPythonListsort.ScanPowerForestInv

namespace CPythonListsort.ScanPowerForestInv

/--
[openSpanChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ScanPowerForestInvariant.lean)
-/
@[path]
lemma openSpanChain
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {state : MergeState κ ν}
-- given
  (h : ScanPowerForestInv input forest state)
  (hlayout : PendingLayout state input.len) :
-- imply
  OpenSpanChain input input.base forest := by
-- proof
  apply openSpanChain_of_cover
    (input := input) (cursor := input.base)
    (limit := state.basekeys + input.len)
    (runs := state.pending.toList)
  · exact Nat.le_refl _
  · simp [RunSpan.endIndex, h.basekeys_eq]
  · simpa [h.basekeys_eq] using hlayout.2.2.2
  · exact h.aligned

end CPythonListsort.ScanPowerForestInv

namespace CPythonListsort.ScanPowerForestInv

/--
[replayBoundaryPower_eq_pendingBoundaryPower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ScanPowerForestInvariant.lean)
-/
@[path]
private lemma replayBoundaryPower_eq_pendingBoundaryPower
  {input : RunSpan} {state : MergeState κ ν}
  {left right : SpannedMergeTree} {leftRun rightRun : PendingRun}
  (hbase : state.basekeys = input.base)
  (hlength : state.listlen = BitVec.ofNat 64 input.len)
  (hleft : RunTreeAligned input left leftRun)
  (hright : RunTreeAligned input right rightRun) :
  replayBoundaryPower input left.span right.span =
    pendingBoundaryPower state.basekeys state.listlen leftRun rightRun := by
  simp [replayBoundaryPower, pendingBoundaryPower, hbase, hlength,
    hleft.span_eq, hright.span_eq, RunSpan.ofPendingRun]

end CPythonListsort.ScanPowerForestInv

namespace CPythonListsort.ScanPowerForestInv

/--
[openBoundaryCertificate_of_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ScanPowerForestInvariant.lean)
-/
@[path]
private lemma openBoundaryCertificate_of_aligned
  {input : RunSpan} {state : MergeState κ ν}
  {forest : List SpannedMergeTree} {runs : List PendingRun}
  {powers : List Nat}
  (hbase : state.basekeys = input.base)
  (hlength : state.listlen = BitVec.ofNat 64 input.len)
  (haligned : List.Forall₂ (RunTreeAligned input) forest runs)
  (hnewest : NewestRootLeaf forest)
  (hpowerMap : runs.dropLast.map PendingRun.power = powers.map some)
  (hexact : ExactBoundaryPowers state.basekeys state.listlen runs) :
  OpenBoundaryCertificate input forest powers := by
  induction hnewest generalizing runs powers with
  | empty =>
    cases haligned
    cases powers with
    | nil => exact .empty
    | cons power powers => cases hpowerMap
  | singleton span =>
    cases haligned with
    | cons hentry htail =>
      cases htail
      cases powers with
      | nil =>
        exact .singleton (SpannedMergeTree.leaf span) span.len rfl
      | cons power powers => cases hpowerMap
  | prepend entry right rest htail ih =>
    cases haligned with
    | @cons _ leftRun _ runs hleft halignedTail =>
      cases halignedTail with
      | @cons _ rightRun _ remainingRuns hright halignedRest =>
        cases powers with
        | nil => cases hpowerMap
        | cons power powers =>
          simp only [List.dropLast_cons_cons, List.map_cons,
            List.cons.injEq] at hpowerMap
          obtain ⟨hleftPower, hpowerTail⟩ := hpowerMap
          have hhead := ExactBoundaryPowers.head hexact
          have hexactTail := ExactBoundaryPowers.tail hexact
          refine .cons entry right rest power powers ?_ ?_ ?_
          · calc
            power = pendingBoundaryPower state.basekeys state.listlen
              leftRun rightRun := by
                rw [hleftPower] at hhead
                exact Option.some.inj hhead
            _ = replayBoundaryPower input entry.span right.span :=
              (replayBoundaryPower_eq_pendingBoundaryPower
                hbase hlength hleft hright).symm
          · intro rootPower hroot
            exact hleft.outgoingBelowRoot power rootPower
              hleftPower hroot
          · exact ih (List.Forall₂.cons hright halignedRest)
            hpowerTail hexactTail

end CPythonListsort.ScanPowerForestInv

namespace CPythonListsort.ScanPowerForestInv

/--
[openBoundaryCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ScanPowerForestInvariant.lean)
-/
@[path]
lemma openBoundaryCertificate
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {state : MergeState κ ν}
-- given
  (h : ScanPowerForestInv input forest state)
  (hpowered : PoweredPrefix state) :
-- imply
  ∃ powers, OpenBoundaryCertificate input forest powers ∧ powers.Pairwise (fun earlier later => earlier < later) := by
-- proof
  by_cases hempty : state.pending.toList = []
  · have hforest : forest = [] := by
    have hlength := h.aligned.length_eq
    rw [hempty] at hlength
    exact List.eq_nil_of_length_eq_zero (by simpa using hlength)
    subst forest
    exact ⟨[], .empty, by simp⟩
  · rcases hpowered.split_of_nonempty hempty with
    ⟨olderRuns, newest, hruns, hincreasing, hexact⟩
    obtain ⟨powers, hpowerMap, _hrange, hstrict⟩ := hincreasing
    refine ⟨powers, ?_, hstrict⟩
    apply openBoundaryCertificate_of_aligned
      h.basekeys_eq h.listlen_eq h.aligned h.newestRootLeaf
    · rw [hruns]
      simpa using hpowerMap
    · exact hexact

end CPythonListsort.ScanPowerForestInv

namespace CPythonListsort.ScanPowerForestInv

/--
[toPowerOpenForestValid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/ScanPowerForestInvariant.lean)
-/
@[path]
lemma toPowerOpenForestValid
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {state : MergeState κ ν}
-- given
  (h : ScanPowerForestInv input forest state)
  (hlayout : PendingLayout state input.len)
  (hpowered : PoweredPrefix state) :
-- imply
  PowerOpenForestValid input forest := by
-- proof
  rcases h.openBoundaryCertificate hpowered with
    ⟨powers, hboundaries, hstrict⟩
  exact ⟨powers,
    { inputMax := h.inputMax
      spans := h.openSpanChain hlayout
      treeValid := fun entry hentry => h.tree_valid hentry
      boundaries := hboundaries
      strict := hstrict }⟩

end CPythonListsort.ScanPowerForestInv


-- created on 2026-10-23
