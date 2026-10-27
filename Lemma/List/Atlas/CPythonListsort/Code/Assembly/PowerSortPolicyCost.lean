import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.CPythonListsort.Code.Assembly.PowerSortPolicyCost.Part2
open CPythonListsort CPythonListsort.RunSpan
open forest. -/


namespace CPythonListsort.RunSpan

/--
[merge_validWithin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma merge_validWithin
  {input left right : RunSpan}
-- given
  (hleft : left.ValidWithin input)
  (hright : right.ValidWithin input)
  (hadjacent : left.Adjacent right) :
-- imply
  (left.merge right).ValidWithin input := by
-- proof
  obtain ⟨hleftBase, _hleftEnd, hleftPositive⟩ := hleft
  obtain ⟨_rightBase, hrightEnd, hrightPositive⟩ := hright
  refine ⟨?_, ?_, ?_⟩
  · simpa [RunSpan.merge] using hleftBase
  · simp only [RunSpan.Adjacent, RunSpan.endIndex] at hadjacent
    simp only [RunSpan.endIndex, RunSpan.merge] at hrightEnd ⊢
    omega
  · simp only [RunSpan.merge]
    omega

end CPythonListsort.RunSpan

namespace CPythonListsort

/--
[replayBoundaryPower_absorb_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma replayBoundaryPower_absorb_right
  {input left middle right : RunSpan}
-- given
  (hinputMax : input.len ≤ PY_LIST_MAX)
  (hleft : left.ValidWithin input)
  (hmiddle : middle.ValidWithin input)
  (hright : right.ValidWithin input)
  (hleftMiddle : left.Adjacent middle)
  (hmiddleRight : middle.Adjacent right)
  (hpower : replayBoundaryPower input left middle < replayBoundaryPower input middle right) :
-- imply
  replayBoundaryPower input left (middle.merge right) = replayBoundaryPower input left middle := by
-- proof
  let s := left.base - input.base
  have hleftBase : input.base ≤ left.base := hleft.1
  have hmiddleBase : middle.base - input.base = s + left.len := by
    dsimp [s]
    unfold RunSpan.Adjacent RunSpan.endIndex at hleftMiddle
    omega
  have hfits : s + left.len + middle.len + right.len ≤ input.len := by
    dsimp [s]
    unfold RunSpan.ValidWithin RunSpan.endIndex at hright
    unfold RunSpan.Adjacent RunSpan.endIndex at hleftMiddle hmiddleRight
    omega
  have hgeometry := boundaryPowerGeometry s left.len middle.len right.len
    input.len hleft.2.2 hmiddle.2.2 hright.2.2 hfits hinputMax
  dsimp only at hgeometry
  have hpower' :
    powerloop (BitVec.ofNat 64 s) (BitVec.ofNat 64 left.len)
      (BitVec.ofNat 64 middle.len) (BitVec.ofNat 64 input.len) <
      powerloop (BitVec.ofNat 64 (s + left.len))
        (BitVec.ofNat 64 middle.len) (BitVec.ofNat 64 right.len)
        (BitVec.ofNat 64 input.len) := by
    simpa [replayBoundaryPower, s, hmiddleBase] using hpower
  have habsorb := hgeometry.2.1 hpower'
  simpa [replayBoundaryPower, RunSpan.merge, s] using habsorb

end CPythonListsort

namespace CPythonListsort

/--
[replayBoundaryPower_absorb_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma replayBoundaryPower_absorb_left
  {input left middle right : RunSpan}
-- given
  (hinputMax : input.len ≤ PY_LIST_MAX)
  (hleft : left.ValidWithin input)
  (hmiddle : middle.ValidWithin input)
  (hright : right.ValidWithin input)
  (hleftMiddle : left.Adjacent middle)
  (hmiddleRight : middle.Adjacent right)
  (hpower : replayBoundaryPower input middle right < replayBoundaryPower input left middle) :
-- imply
  replayBoundaryPower input (left.merge middle) right = replayBoundaryPower input middle right := by
-- proof
  let s := left.base - input.base
  have hleftBase : input.base ≤ left.base := hleft.1
  have hmiddleBase : middle.base - input.base = s + left.len := by
    dsimp [s]
    unfold RunSpan.Adjacent RunSpan.endIndex at hleftMiddle
    omega
  have hfits : s + left.len + middle.len + right.len ≤ input.len := by
    dsimp [s]
    unfold RunSpan.ValidWithin RunSpan.endIndex at hright
    unfold RunSpan.Adjacent RunSpan.endIndex at hleftMiddle hmiddleRight
    omega
  have hgeometry := boundaryPowerGeometry s left.len middle.len right.len
    input.len hleft.2.2 hmiddle.2.2 hright.2.2 hfits hinputMax
  dsimp only at hgeometry
  have hpower' :
    powerloop (BitVec.ofNat 64 (s + left.len))
      (BitVec.ofNat 64 middle.len) (BitVec.ofNat 64 right.len)
      (BitVec.ofNat 64 input.len) <
      powerloop (BitVec.ofNat 64 s) (BitVec.ofNat 64 left.len)
        (BitVec.ofNat 64 middle.len) (BitVec.ofNat 64 input.len) := by
    simpa [replayBoundaryPower, s, hmiddleBase] using hpower
  have habsorb := hgeometry.2.2 hpower'
  have hmergedBase : (left.merge middle).base - input.base = s := by
    simp [RunSpan.merge, s]
  simpa [replayBoundaryPower, RunSpan.merge, s, hmiddleBase,
    hmergedBase] using habsorb

end CPythonListsort

namespace CPythonListsort

/--
[canonicalTopPairCompletion_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma canonicalTopPairCompletion_empty
  {input : RunSpan} :
-- imply
  canonicalTopPairCompletion input [] = .empty :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[canonicalTopPairCompletion_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma canonicalTopPairCompletion_singleton
  {input : RunSpan}
  {entry : SpannedMergeTree} :
-- imply
  canonicalTopPairCompletion input [entry] = .tree entry.tree :=
-- proof
  rfl

end CPythonListsort

namespace CPythonListsort

/--
[canonicalTopPairRoot_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma canonicalTopPairRoot_base
  {input : RunSpan}
  {first : SpannedMergeTree}
  {rest : List SpannedMergeTree} :
-- imply
  (canonicalTopPairRoot input first rest).span.base = first.span.base := by
-- proof
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih =>
    simp [canonicalTopPairRoot, SpannedMergeTree.merge, RunSpan.merge]

end CPythonListsort

namespace CPythonListsort

/--
[canonicalTopPairRoot_span_len](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma canonicalTopPairRoot_span_len
  {input : RunSpan}
  {first : SpannedMergeTree}
  {rest : List SpannedMergeTree} :
-- imply
  (canonicalTopPairRoot input first rest).span.len = (openForestLengths (first :: rest)).sum := by
-- proof
  induction rest generalizing first with
  | nil => simp [canonicalTopPairRoot, openForestLengths]
  | cons next rest ih =>
    simp only [canonicalTopPairRoot, SpannedMergeTree.merge, RunSpan.merge,
      openForestLengths, List.map_cons, List.sum_cons]
    rw [ih]
    simp [openForestLengths]

end CPythonListsort

namespace CPythonListsort

/--
[canonicalTopPairRoot_runLengths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma canonicalTopPairRoot_runLengths
  {input : RunSpan}
  {first : SpannedMergeTree}
  {rest : List SpannedMergeTree} :
-- imply
  (canonicalTopPairRoot input first rest).tree.runLengths = forestRunLengths (first :: rest) := by
-- proof
  induction rest generalizing first with
  | nil => simp [canonicalTopPairRoot, forestRunLengths]
  | cons next rest ih =>
    simp only [canonicalTopPairRoot, SpannedMergeTree.merge,
      MergeTree.runLengths, forestRunLengths_cons]
    rw [ih]
    rfl

end CPythonListsort

namespace CPythonListsort

/--
[canonicalTopPairCompletion_runLengths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma canonicalTopPairCompletion_runLengths
  {input : RunSpan}
  {forest : List SpannedMergeTree} :
-- imply
  (canonicalTopPairCompletion input forest).runLengths = forestRunLengths forest := by
-- proof
  cases forest with
  | nil => rfl
  | cons first rest =>
    exact canonicalTopPairRoot_runLengths input first rest

end CPythonListsort

namespace CPythonListsort

/--
[canonicalTopPairRoot_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma canonicalTopPairRoot_valid
  {input : RunSpan}
  {first : SpannedMergeTree}
  {rest : List SpannedMergeTree}
-- given
  (hvalid : ∀ entry ∈ first :: rest, entry.Valid) :
-- imply
  (canonicalTopPairRoot input first rest).Valid := by
-- proof
  induction rest generalizing first with
  | nil => exact hvalid first (by simp)
  | cons next rest ih =>
    simp only [canonicalTopPairRoot]
    apply SpannedMergeTree.merge_valid
    · exact hvalid first (by simp)
    · apply ih
      intro entry hentry
      exact hvalid entry (by simp [hentry])

end CPythonListsort

namespace CPythonListsort

/--
[canonicalTopPairRoot_mergeCost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma canonicalTopPairRoot_mergeCost
  {input : RunSpan}
  {first : SpannedMergeTree}
  {rest : List SpannedMergeTree}
-- given
  (hvalid : ∀ entry ∈ first :: rest, entry.Valid) :
-- imply
  (canonicalTopPairRoot input first rest).tree.mergeCost = forestMergeCost (first :: rest) + topPairCompletionCost (openForestLengths (first :: rest)) := by
-- proof
  induction rest generalizing first with
  | nil => simp [canonicalTopPairRoot, openForestLengths,
    forestMergeCost, topPairCompletionCost]
  | cons next rest ih =>
    have hfirst := hvalid first (by simp)
    have htail : ∀ entry ∈ next :: rest, entry.Valid := by
      intro entry hentry
      exact hvalid entry (by simp [hentry])
    have hrightValid := canonicalTopPairRoot_valid input next rest htail
    have hrightLength := canonicalTopPairRoot_span_len input next rest
    simp only [canonicalTopPairRoot, SpannedMergeTree.merge,
      MergeTree.mergeCost, forestMergeCost,
      openForestLengths, List.map_cons, List.sum_cons]
    rw [ih next htail]
    simp only [SpannedMergeTree.Valid] at hfirst hrightValid
    rw [hfirst, hrightValid, hrightLength]
    cases rest with
    | nil =>
      simp [openForestLengths, forestMergeCost, topPairCompletionCost]
      omega
    | cons third tail =>
      simp [openForestLengths, forestMergeCost, topPairCompletionCost]
      omega

end CPythonListsort

namespace CPythonListsort

/--
[canonicalTopPairCompletion_mergeCost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma canonicalTopPairCompletion_mergeCost
  {input : RunSpan}
  {forest : List SpannedMergeTree}
-- given
  (hvalid : ∀ entry ∈ forest, entry.Valid) :
-- imply
  (canonicalTopPairCompletion input forest).mergeCost = forestMergeCost forest + topPairCompletionCost (openForestLengths forest) := by
-- proof
  cases forest with
  | nil => rfl
  | cons first rest =>
    exact canonicalTopPairRoot_mergeCost input first rest hvalid

end CPythonListsort

namespace CPythonListsort

/--
[canonicalTopPairRoot_span_of_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma canonicalTopPairRoot_span_of_chain
  {input : RunSpan}
  {start : Nat}
  {first : SpannedMergeTree}
  {rest : List SpannedMergeTree}
-- given
  (hchain : OpenSpanChain input start (first :: rest)) :
-- imply
  let root := canonicalTopPairRoot input first rest root.span.base = start ∧ root.span.endIndex = input.endIndex ∧ root.span.ValidWithin input := by
-- proof
  induction rest generalizing start first with
  | nil =>
    cases hchain with
    | cons entry rest hbase hvalid htail =>
      cases htail with
      | empty hend =>
        exact ⟨hbase, hend, hvalid⟩
  | cons next rest ih =>
    cases hchain with
    | cons entry tail hbase hvalid htail =>
      have hright := ih htail
      dsimp only at hright ⊢
      have hadjacent : first.span.Adjacent
        (canonicalTopPairRoot input next rest).span := by
        unfold RunSpan.Adjacent
        rw [hright.1]
      have hend :
        (SpannedMergeTree.merge
          (replayBoundaryPower input first.span
            (canonicalTopPairRoot input next rest).span)
          first (canonicalTopPairRoot input next rest)).span.endIndex =
          input.endIndex := by
        calc
          _ = first.span.endIndex +
            (canonicalTopPairRoot input next rest).span.len := by
            simp [SpannedMergeTree.merge, RunSpan.merge,
              RunSpan.endIndex, Nat.add_assoc]
          _ = (canonicalTopPairRoot input next rest).span.base +
            (canonicalTopPairRoot input next rest).span.len := by
            rw [hadjacent]
          _ = (canonicalTopPairRoot input next rest).span.endIndex := rfl
          _ = input.endIndex := hright.2.1
      refine ⟨?_, ?_, ?_⟩
      · simpa [canonicalTopPairRoot, SpannedMergeTree.merge,
        RunSpan.merge] using hbase
      · simpa [canonicalTopPairRoot] using hend
      · apply RunSpan.merge_validWithin hvalid hright.2.2 hadjacent

end CPythonListsort

namespace CPythonListsort

/--
[inputWord_toNat_of_max](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
private lemma inputWord_toNat_of_max {input : RunSpan}
  (hmax : input.len ≤ PY_LIST_MAX) :
  (BitVec.ofNat 64 input.len).toNat = input.len := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  rw [pyListMax_eq] at hmax
  norm_num at hmax ⊢
  omega

end CPythonListsort

namespace CPythonListsort

/--
[replayBoundaryPower_valid_input](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma replayBoundaryPower_valid_input
  {input left right : RunSpan}
-- given
  (hinputMax : input.len ≤ PY_LIST_MAX)
  (hleft : left.ValidWithin input)
  (hright : right.ValidWithin input)
  (hadjacent : left.Adjacent right) :
-- imply
  ValidPowerloopInput (BitVec.ofNat 64 (left.base - input.base)) (BitVec.ofNat 64 left.len) (BitVec.ofNat 64 right.len) (BitVec.ofNat 64 input.len) := by
-- proof
  apply validPowerloopInput_ofNat hleft.2.2 hright.2.2
  · unfold RunSpan.ValidWithin RunSpan.endIndex at hleft hright
    unfold RunSpan.Adjacent RunSpan.endIndex at hadjacent
    omega
  · exact hinputMax

end CPythonListsort

namespace CPythonListsort

/--
[canonicalTopPairRoot_of_open_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
private lemma canonicalTopPairRoot_of_open_certificate
  {input : RunSpan} {start : Nat}
  {first : SpannedMergeTree} {rest : List SpannedMergeTree}
  {powers : List Nat}
  (hinputMax : input.len ≤ PY_LIST_MAX)
  (hspans : OpenSpanChain input start (first :: rest))
  (htrees : ∀ entry ∈ first :: rest,
    entry.Valid ∧
      entry.tree.PowerValid input.base (BitVec.ofNat 64 input.len)
        entry.span.base)
  (hboundaries : OpenBoundaryCertificate input (first :: rest) powers)
  (hstrict : powers.Pairwise (fun earlier later => earlier < later)) :
  CanonicalTopPairRootPost input start powers
    (canonicalTopPairRoot input first rest) := by
  induction rest generalizing start first powers with
  | nil =>
    cases hboundaries with
    | singleton entry length isLeaf =>
      cases hspans with
      | cons entry rest hbase hspan htail =>
        cases htail with
        | empty hend =>
          have htree := htrees first (by simp)
          refine
            { base_eq := hbase
              end_eq := hend
              spanValid := hspan
              spannedValid := htree.1
              powerValid := by
                simpa [canonicalTopPairRoot, hbase] using htree.2
              rootPower_eq := by
                simp [canonicalTopPairRoot, isLeaf,
                  MergeTree.rootPower] }
  | cons right rest ih =>
    cases hboundaries with
    | cons left right rest power powers hpower hbelow htail =>
      cases hspans with
      | cons entry tail hleftBase hleftSpan hspanTail =>
        have hleftTree := htrees first (by simp)
        have htailTrees : ∀ entry ∈ right :: rest,
          entry.Valid ∧
            entry.tree.PowerValid input.base (BitVec.ofNat 64 input.len)
              entry.span.base := by
          intro entry hentry
          exact htrees entry (by simp [hentry])
        simp only [List.pairwise_cons] at hstrict
        have hrightPost := ih hspanTail htailTrees htail hstrict.2
        have hleftRight : first.span.Adjacent right.span := by
          cases hspanTail with
          | cons right rest hrightBase hrightSpan hrest =>
            unfold RunSpan.Adjacent
            exact hrightBase.symm
        let rightRoot := canonicalTopPairRoot input right rest
        have haggregatePower :
          replayBoundaryPower input first.span rightRoot.span = power := by
          cases rest with
          | nil =>
            cases htail with
            | singleton right length isLeaf =>
              simpa [rightRoot, canonicalTopPairRoot] using hpower.symm
          | cons next tail =>
            cases htail with
            | cons middle next tail nextPower tailPowers
              hnextPower hnextBelow hnextTail =>
              cases hspanTail with
              | cons right rest hrightBase hrightSpan hrestChain =>
                have hrestPost :=
                  canonicalTopPairRoot_span_of_chain hrestChain
                dsimp only at hrestPost
                let restRoot := canonicalTopPairRoot input next tail
                have hrightRest :
                  right.span.Adjacent restRoot.span := by
                  unfold RunSpan.Adjacent
                  simpa [restRoot] using hrestPost.1.symm
                have hnextAggregate :
                  replayBoundaryPower input right.span restRoot.span =
                    nextPower := by
                  have hrootPower := hrightPost.rootPower_eq
                  simpa [rightRoot, restRoot, canonicalTopPairRoot,
                    SpannedMergeTree.merge, MergeTree.rootPower] using
                      hrootPower
                have hpowerLt : power < nextPower :=
                  hstrict.1 nextPower (by simp)
                have habsorb := replayBoundaryPower_absorb_right
                  input first.span right.span restRoot.span hinputMax
                  hleftSpan hrightSpan hrestPost.2.2 hleftRight
                  hrightRest
                  (by simpa [hpower, hnextAggregate] using hpowerLt)
                simpa [rightRoot, restRoot, canonicalTopPairRoot,
                  SpannedMergeTree.merge, RunSpan.merge, hpower] using
                    habsorb
        have hleftAggregate : first.span.Adjacent rightRoot.span := by
          exact hrightPost.base_eq.symm
        have hnewPowerValid :
          (SpannedMergeTree.merge
            (replayBoundaryPower input first.span rightRoot.span)
            first rightRoot).tree.PowerValid input.base
              (BitVec.ofNat 64 input.len) start := by
          simp only [SpannedMergeTree.merge, MergeTree.PowerValid]
          have hword := inputWord_toNat_of_max hinputMax
          have hleftLen : first.tree.totalLength = first.span.len :=
            hleftTree.1
          have hrightLen : rightRoot.tree.totalLength =
            rightRoot.span.len := hrightPost.spannedValid
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simpa [hleftBase] using hleftSpan.1
          · rw [hword]
            have hend : rightRoot.span.endIndex = input.endIndex := by
              simpa [rightRoot] using hrightPost.end_eq
            unfold RunSpan.Adjacent RunSpan.endIndex at hleftAggregate
            unfold RunSpan.ValidWithin RunSpan.endIndex at hleftSpan
            unfold RunSpan.endIndex at hend
            rw [hleftLen, hrightLen]
            omega
          · simpa [hleftBase] using hleftTree.2
          · have hstartRight :
            start + first.tree.totalLength =
              first.span.endIndex := by
            unfold RunSpan.endIndex
            rw [hleftLen]
            omega
            rw [hstartRight]
            simpa [rightRoot] using hrightPost.powerValid
          · simpa [hleftBase, hleftLen, hrightLen] using
            replayBoundaryPower_valid_input input first.span
              rightRoot.span hinputMax hleftSpan
              hrightPost.spanValid hleftAggregate
          · simp [replayBoundaryPower, hleftBase, hleftLen, hrightLen]
          · intro childPower hchild
            rw [haggregatePower]
            exact hbelow childPower hchild
          · intro childPower hchild
            rw [haggregatePower]
            cases hpowers : powers with
            | nil =>
              have : rightRoot.tree.rootPower = none := by
                simpa [hpowers] using hrightPost.rootPower_eq
              rw [this] at hchild
              contradiction
            | cons nextPower tailPowers =>
              have hroot : rightRoot.tree.rootPower = some nextPower := by
                simpa [hpowers] using hrightPost.rootPower_eq
              rw [hroot] at hchild
              cases hchild
              exact hstrict.1 childPower (by simp [hpowers])
        have hspanPost := canonicalTopPairRoot_span_of_chain
          (OpenSpanChain.cons first (right :: rest) hleftBase hleftSpan
            hspanTail)
        dsimp only at hspanPost
        refine
          { base_eq := hspanPost.1
            end_eq := hspanPost.2.1
            spanValid := hspanPost.2.2
            spannedValid := canonicalTopPairRoot_valid input first
              (right :: rest)
              (fun entry hentry => (htrees entry hentry).1)
            powerValid := ?_
            rootPower_eq := ?_ }
        · simpa [rightRoot, canonicalTopPairRoot] using hnewPowerValid
        · simp [rightRoot, canonicalTopPairRoot, SpannedMergeTree.merge,
          MergeTree.rootPower, haggregatePower]

end CPythonListsort

namespace CPythonListsort

/--
[PowerOpenForestCertificate.canonicalCompletion_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma PowerOpenForestCertificate.canonicalCompletion_valid
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {powers : List Nat}
  {certificate : PowerOpenForestCertificate input input.base forest powers} :
-- imply
  PowerMergePlanValid input.base (BitVec.ofNat 64 input.len) (canonicalTopPairCompletion input forest) := by
-- proof
  cases forest with
  | nil =>
    cases certificate.spans with
    | empty hend =>
      simp only [canonicalTopPairCompletion, PowerMergePlanValid]
      have hword := inputWord_toNat_of_max certificate.inputMax
      rw [hword]
      unfold RunSpan.endIndex at hend
      omega
  | cons first rest =>
    have hpost := canonicalTopPairRoot_of_open_certificate
      certificate.inputMax certificate.spans certificate.treeValid
      certificate.boundaries certificate.strict
    simp only [canonicalTopPairCompletion, PowerMergePlanValid]
    refine ⟨?_, ?_⟩
    · simpa [hpost.base_eq] using hpost.powerValid
    · have hword := inputWord_toNat_of_max certificate.inputMax
      rw [hword]
      have hvalid := hpost.spannedValid
      simp only [SpannedMergeTree.Valid] at hvalid
      have hbase := hpost.base_eq
      have hend := hpost.end_eq
      unfold RunSpan.endIndex at hend
      rw [hvalid]
      omega

end CPythonListsort

namespace CPythonListsort

/--
[PowerOpenForestValid.canonicalCompletion_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma PowerOpenForestValid.canonicalCompletion_valid
  {input : RunSpan}
  {forest : List SpannedMergeTree}
-- given
  (hvalid : PowerOpenForestValid input forest) :
-- imply
  PowerMergePlanValid input.base (BitVec.ofNat 64 input.len) (canonicalTopPairCompletion input forest) := by
-- proof
  obtain ⟨powers, certificate⟩ := hvalid
  exact certificate.canonicalCompletion_valid

end CPythonListsort

namespace CPythonListsort

/--
[PowerOpenForestCertificate.canonicalCompletion_cost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma PowerOpenForestCertificate.canonicalCompletion_cost
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {powers : List Nat}
  {certificate : PowerOpenForestCertificate input input.base forest powers} :
-- imply
  (canonicalTopPairCompletion input forest).mergeCost = forestMergeCost forest + topPairCompletionCost (openForestLengths forest) :=
-- proof
  canonicalTopPairCompletion_mergeCost input forest
    (fun entry hentry => (certificate.treeValid entry hentry).1)

end CPythonListsort

namespace CPythonListsort

/--
[PowerOpenForestCertificate.canonicalCompletion_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma PowerOpenForestCertificate.canonicalCompletion_spec
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {powers : List Nat}
  {certificate : PowerOpenForestCertificate input input.base forest powers} :
-- imply
  PowerMergePlanValid input.base (BitVec.ofNat 64 input.len) (canonicalTopPairCompletion input forest) ∧ (canonicalTopPairCompletion input forest).mergeCost = forestMergeCost forest + topPairCompletionCost (openForestLengths forest) :=
-- proof
  ⟨certificate.canonicalCompletion_valid,
    certificate.canonicalCompletion_cost⟩

end CPythonListsort

namespace CPythonListsort

/--
[PowerOpenForestValid.canonicalCompletion_cost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma PowerOpenForestValid.canonicalCompletion_cost
  {input : RunSpan}
  {forest : List SpannedMergeTree}
-- given
  (hvalid : PowerOpenForestValid input forest) :
-- imply
  (canonicalTopPairCompletion input forest).mergeCost = forestMergeCost forest + topPairCompletionCost (openForestLengths forest) := by
-- proof
  obtain ⟨powers, certificate⟩ := hvalid
  exact certificate.canonicalCompletion_cost

end CPythonListsort

namespace CPythonListsort

/--
[PowerOpenForestValid.canonicalCompletion_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma PowerOpenForestValid.canonicalCompletion_spec
  {input : RunSpan}
  {forest : List SpannedMergeTree}
-- given
  (hvalid : PowerOpenForestValid input forest) :
-- imply
  PowerMergePlanValid input.base (BitVec.ofNat 64 input.len) (canonicalTopPairCompletion input forest) ∧ (canonicalTopPairCompletion input forest).mergeCost = forestMergeCost forest + topPairCompletionCost (openForestLengths forest) := by
-- proof
  obtain ⟨powers, certificate⟩ := hvalid
  exact certificate.canonicalCompletion_spec

end CPythonListsort

namespace CPythonListsort

/--
[PowerOpenForestCertificate.cpythonForceCollapseCost_le_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma PowerOpenForestCertificate.cpythonForceCollapseCost_le_canonical
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {powers : List Nat}
  {collapseCost : Nat}
  {certificate : PowerOpenForestCertificate input input.base forest powers}
-- given
  (hcollapse : CPythonForceCollapseCost (openForestLengths forest) collapseCost) :
-- imply
  forestMergeCost forest + collapseCost ≤ (canonicalTopPairCompletion input forest).mergeCost := by
-- proof
  rw [canonicalTopPairCompletion_mergeCost input forest
    (fun entry hentry => (certificate.treeValid entry hentry).1)]
  exact Nat.add_le_add_left hcollapse.le_topPairCompletionCost _

end CPythonListsort

namespace CPythonListsort

/--
[PowerOpenForestValid.cpythonForceCollapseCost_le_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortPolicyCost.lean)
-/
@[path]
lemma PowerOpenForestValid.cpythonForceCollapseCost_le_canonical
  {input : RunSpan}
  {forest : List SpannedMergeTree}
  {collapseCost : Nat}
-- given
  (hvalid : PowerOpenForestValid input forest)
  (hcollapse : CPythonForceCollapseCost (openForestLengths forest) collapseCost) :
-- imply
  forestMergeCost forest + collapseCost ≤ (canonicalTopPairCompletion input forest).mergeCost := by
-- proof
  obtain ⟨powers, certificate⟩ := hvalid
  exact certificate.cpythonForceCollapseCost_le_canonical hcollapse

end CPythonListsort


-- created on 2026-10-23
