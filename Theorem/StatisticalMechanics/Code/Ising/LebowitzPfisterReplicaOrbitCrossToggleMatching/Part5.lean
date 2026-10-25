/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part21
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part5
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaDecoratedSourceCanonicalHalfCandidate_allocation
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    (lpReplicaDecoratedSourceCanonicalHalfCandidate
        G sites hsite hij q z).2.allocation =
      fun e => ((lpReplicaProfileOrbitLabelPartialReflectCopies G sites q
        z.1.1.1 z.1.1.2
        (lpReplicaDecoratedSourceCanonicalHalfSelector
          G sites i j q z).selector z.2.2) e).1 := by
  unfold lpReplicaDecoratedSourceCanonicalHalfCandidate
    lpReplicaDecoratedSourceCanonicalHalfSlotMask
    lpReplicaOffdiagDecoratedSourceSlotState
    lpReplicaOrientedFourColorSlotState
  exact lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_allocation
    G sites q z.1.1.1 z.1.1.2 z.2.2
      (lpReplicaDecoratedSourceCanonicalHalfSelector
        G sites i j q z).selector
      (lpReplicaOrientedFourColorTag G sites ∅
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q z))


theorem lpReplicaDecoratedSourceCanonicalHalfCandidate_color
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    (lpReplicaDecoratedSourceCanonicalHalfCandidate
        G sites hsite hij q z).2.color =
      (lpReplicaOrbitFourColorSlotStateOfTag G sites q z.1.1.1
        z.1.1.2 z.2.2
        (lpReplicaToggleRows G sites z.1.1.1
          (lpReplicaDecoratedSourceCanonicalHalfSelector
            G sites i j q z).selector
          (lpReplicaOrientedFourColorTag G sites ∅
            (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
              lpMatchingSeamSource
                (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
              lpMatchingGhostSource
                (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                lpReplicaCurrentGhost1) q
            (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅
              (lpMatchingSeamSource
                  (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
                lpMatchingSeamSource
                  (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
                lpMatchingGhostSource
                  (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                  lpReplicaCurrentGhost1) q z)))).color := by
  unfold lpReplicaDecoratedSourceCanonicalHalfCandidate
    lpReplicaDecoratedSourceCanonicalHalfSlotMask
    lpReplicaOffdiagDecoratedSourceSlotState
    lpReplicaOrientedFourColorSlotState
  exact lpReplicaOrbitFourColorSlotCrossToggle_ofCopies_color
    G sites q z.1.1.1 z.1.1.2 z.2.2
      (lpReplicaDecoratedSourceCanonicalHalfSelector
        G sites i j q z).selector
      (lpReplicaOrientedFourColorTag G sites ∅
        (lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1) q
        (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites ∅
          (lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
            lpMatchingSeamSource
              (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
            lpMatchingGhostSource
              (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
              lpReplicaCurrentGhost1) q z))

set_option maxHeartbeats 800000 in


theorem lpReplicaDecoratedSourceCanonicalHalfCandidate_eq_iff
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z w : LPReplicaOffdiagDecoratedSource G sites i j q) :
    lpReplicaDecoratedSourceCanonicalHalfCandidate
        G sites hsite hij q z =
      lpReplicaDecoratedSourceCanonicalHalfCandidate
        G sites hsite hij q w ↔
      lpReplicaDecoratedSourceCanonicalHalfBranchBit
          G sites hsite hij q z =
        lpReplicaDecoratedSourceCanonicalHalfBranchBit
          G sites hsite hij q w ∧
      lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z =
        lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q w ∧
      lpReplicaOrbitFourColorSlotRowMask G sites q
            (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) ∆
          lpReplicaDecoratedSourceCanonicalHalfSlotMask G sites i j q z =
        lpReplicaOrbitFourColorSlotRowMask G sites q
            (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w) ∆
          lpReplicaDecoratedSourceCanonicalHalfSlotMask G sites i j q w := by
  unfold lpReplicaDecoratedSourceCanonicalHalfCandidate
  constructor
  · intro h
    refine ⟨congrArg Prod.fst h, ?_⟩
    have hstate := congrArg Prod.snd h
    exact (lpReplicaOrbitFourColorSlotCrossToggle_eq_iff G sites q
      (lpReplicaDecoratedSourceCanonicalHalfSlotMask G sites i j q z)
      (lpReplicaDecoratedSourceCanonicalHalfSlotMask G sites i j q w)
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w)).mp hstate
  · rintro ⟨hbranch, htrace, hrow⟩
    apply Prod.ext hbranch
    exact (lpReplicaOrbitFourColorSlotCrossToggle_eq_iff G sites q
      (lpReplicaDecoratedSourceCanonicalHalfSlotMask G sites i j q z)
      (lpReplicaDecoratedSourceCanonicalHalfSlotMask G sites i j q w)
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q w)).mpr
        ⟨htrace, hrow⟩


theorem isEmpty_lpReplicaOrbitCommonSlot_zero
    (G : SimpleGraph V) (sites : I -> V) :
    IsEmpty (LPReplicaOrbitCommonSlot G sites (fun _ => 0)) := by
  constructor
  intro x
  rcases x with ⟨fixed, k⟩ | ⟨strict, k⟩
  · have hk : (fun _ : (lpReplicaCurrentGraph G sites).edgeFinset => 0)
        fixed.1 / 2 = 0 := by simp
    exact Fin.elim0 (Fin.cast hk k)
  · exact Fin.elim0 k


theorem isEmpty_lpReplicaOffdiagDecoratedSource_zero
    (G : SimpleGraph V) (sites : I -> V) (i j : I) :
    IsEmpty (LPReplicaOffdiagDecoratedSource G sites i j (fun _ => 0)) := by
  constructor
  intro z
  let d := lpReplicaDecoratedSourceRowGateData
    G sites i j (fun _ => 0) z
  have hmle : z.1.1.1 <= (fun _ => 0) :=
    lpReplicaProfile_le_of_symmetrizedProfile_eq G sites z.1.1.2
  have hmzero : z.1.1.1 = (fun _ => 0) := by
    funext e
    exact Nat.le_zero.mp (hmle e)
  have hcopies : lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false = ∅ := by
    ext c
    have hc : False := by
      rcases c with ⟨e, k⟩
      have hk : z.1.1.1 e = 0 := congrFun hmzero e
      exact Fin.elim0 (Fin.cast hk k)
    exact False.elim hc
  have hboundary :
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 = ∅ := by
    rw [← d.2.2.2.2.1, hcopies]
    simp [StatMech.Sharpness.RandomCurrent.sources,
      StatMech.Sharpness.RandomCurrent.degK]
  have hghost : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := by
    simp [lpMatchingSeamSource, lpMatchingGhostSource,
      lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
      Finset.mem_symmDiff]
  rw [hboundary] at hghost
  simp at hghost


theorem lpReplicaOffdiagCrossToggleMaskHall_zero
    (G : SimpleGraph V) (sites : I -> V) (i j : I) :
    LPReplicaOffdiagCrossToggleMaskHall G sites i j (fun _ => 0) := by
  classical
  unfold LPReplicaOffdiagCrossToggleMaskHall
  intro S
  have hS : S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z _
    exact (isEmpty_lpReplicaOffdiagDecoratedSource_zero G sites i j).false z
  simp [hS]


theorem randomCurrent_sources_subset_endpointSupport
    {E W : Type*} [Fintype E] [DecidableEq E]
    [Fintype W] [DecidableEq W]
    (ends : E -> Sym2 W) (K : Finset E) :
    StatMech.Sharpness.RandomCurrent.sources ends K ⊆
      K.biUnion fun e => (ends e).toFinset := by
  classical
  intro x hx
  rw [StatMech.Sharpness.RandomCurrent.mem_sources] at hx
  have hne : StatMech.Sharpness.RandomCurrent.degK ends K x ≠ 0 := by
    rcases hx with ⟨n, hn⟩
    omega
  have hfilter : (K.filter fun e => x ∈ ends e).Nonempty := by
    rw [← Finset.card_pos]
    exact Nat.pos_of_ne_zero hne
  obtain ⟨e, he⟩ := hfilter
  obtain ⟨heK, hxe⟩ := Finset.mem_filter.mp he
  apply Finset.mem_biUnion.mpr
  exact ⟨e, heK, Sym2.mem_toFinset.mpr hxe⟩


theorem card_randomCurrent_sources_le_two_mul_card
    {E W : Type*} [Fintype E] [DecidableEq E]
    [Fintype W] [DecidableEq W]
    (ends : E -> Sym2 W) (K : Finset E) :
    (StatMech.Sharpness.RandomCurrent.sources ends K).card <= 2 * K.card := by
  classical
  let support : Finset W := K.biUnion fun e => (ends e).toFinset
  calc
    _ <= support.card := Finset.card_le_card
      (randomCurrent_sources_subset_endpointSupport ends K)
    _ <= ∑ e ∈ K, (ends e).toFinset.card := Finset.card_biUnion_le
    _ <= ∑ _e ∈ K, 2 := by
      apply Finset.sum_le_sum
      intro e _
      rw [Sym2.card_toFinset]
      split <;> omega
    _ = 2 * K.card := by simp [Nat.mul_comm]


omit [Fintype V] [Fintype I] [DecidableEq I] in
theorem card_lpReplica_offdiagSource
    (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j) :
    (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1).card = 6 := by
  have hsij : sites i ≠ sites j := hsite.ne hij
  have hi : ({lpReplicaCurrentLeft sites i} :
      Finset (LPReplicaCurrentVertex V)) ∆
        {lpReplicaCurrentRight sites i} =
      {lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i} := by
    rw [Finset.symmDiff_eq_union]
    · rfl
    · simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]
  have hj : ({lpReplicaCurrentLeft sites j} :
      Finset (LPReplicaCurrentVertex V)) ∆
        {lpReplicaCurrentRight sites j} =
      {lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j} := by
    rw [Finset.symmDiff_eq_union]
    · rfl
    · simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]
  have hg : ({(lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)} :
      Finset (LPReplicaCurrentVertex V)) ∆ {lpReplicaCurrentGhost1} =
      {(lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V),
        lpReplicaCurrentGhost1} := by
    rw [Finset.symmDiff_eq_union]
    · rfl
    · simp [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1]
  have hdij : Disjoint
      ({lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i} :
        Finset (LPReplicaCurrentVertex V))
      {lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j} := by
    simp [lpReplicaCurrentLeft, lpReplicaCurrentRight, hsij.symm]
  have hdghost : Disjoint
      (({lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i} :
          Finset (LPReplicaCurrentVertex V)) ∪
        {lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j})
      {(lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V),
        lpReplicaCurrentGhost1} := by
    simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
      lpReplicaCurrentGhost0, lpReplicaCurrentGhost1]
  unfold lpMatchingSeamSource lpMatchingGhostSource
  rw [hi, hj, hg]
  rw [Finset.symmDiff_eq_union hdij,
    Finset.symmDiff_eq_union hdghost]
  simp [lpReplicaCurrentLeft, lpReplicaCurrentRight,
    lpReplicaCurrentGhost0, lpReplicaCurrentGhost1, hsij, hsij.symm]


theorem isEmpty_lpReplicaOffdiagDecoratedSource_of_commonSlotCard_le_two
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) <= 2) :
    IsEmpty (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  constructor
  intro z
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  have hKcard : K.card <= 2 := by
    calc
      K.card <= Fintype.card
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) z.1.1.1) :=
        Finset.card_le_univ K
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2)
      _ <= 2 := hcard
  have hsources : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) z.1.1.1) K =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := d.2.2.2.2.1
  have hsourceCard := card_randomCurrent_sources_le_two_mul_card
    (StatMech.Sharpness.FluxEdgeCopy.endsM
      (lpReplicaCurrentGraph G sites) z.1.1.1) K
  rw [hsources, card_lpReplica_offdiagSource sites hsite hij] at hsourceCard
  omega


theorem lpReplicaOffdiagCrossToggleMaskHall_of_commonSlotCard_le_two
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) <= 2) :
    LPReplicaOffdiagCrossToggleMaskHall G sites i j q := by
  classical
  unfold LPReplicaOffdiagCrossToggleMaskHall
  intro S
  have hS : S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z _
    exact (isEmpty_lpReplicaOffdiagDecoratedSource_of_commonSlotCard_le_two
      G sites hsite hij q hcard).false z
  simp [hS]


theorem lpReplicaOffdiagDecoratedSource_rank_three_all_falseCopies
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 3)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false = Finset.univ ∧
      ∀ c, d.1 c = (true, false) := by
  dsimp only
  let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
  let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
  have hcopyCard : Fintype.card
      (StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) z.1.1.1) = 3 := by
    calc
      _ = Fintype.card (LPReplicaOrbitCommonSlot G sites q) :=
        Fintype.card_congr
          (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
            z.1.1.2 z.2.2)
      _ = 3 := hcard
  have hKle : K.card <= 3 := by
    calc
      K.card <= Fintype.card
          (StatMech.Sharpness.FluxEdgeCopy.Copy
            (lpReplicaCurrentGraph G sites) z.1.1.1) :=
        Finset.card_le_univ K
      _ = 3 := hcopyCard
  have hsources : StatMech.Sharpness.RandomCurrent.sources
      (StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) z.1.1.1) K =
      lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
          lpMatchingSeamSource
            (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
          lpMatchingGhostSource
            (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
            lpReplicaCurrentGhost1 := d.2.2.2.2.1
  have hsourceCard := card_randomCurrent_sources_le_two_mul_card
    (StatMech.Sharpness.FluxEdgeCopy.endsM
      (lpReplicaCurrentGraph G sites) z.1.1.1) K
  rw [hsources, card_lpReplica_offdiagSource sites hsite hij] at hsourceCard
  have hKcard : K.card = 3 := by omega
  have hKuniv : K = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ K)
    rw [Finset.card_univ, hcopyCard, hKcard]
  refine ⟨hKuniv, ?_⟩
  intro c
  have hc : c ∈ K := by rw [hKuniv]; simp
  simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
    Finset.mem_univ, true_and] using hc


theorem lpReplicaOffdiagDecoratedSource_eq_of_crossTrace_eq_of_isEmptySlots
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    [IsEmpty (LPReplicaOrbitCommonSlot G sites q)]
    (z w : LPReplicaOffdiagDecoratedSource G sites i j q)
    (htrace : lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z =
      lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q w) :
    z = w := by
  apply lpReplicaOffdiagDecoratedSourceSlotState_injective G sites i j q
  rw [lpReplicaOrbitFourColorSlotState_eq_iff_crossNormalize_eq_and_rowMask_eq]
  refine ⟨htrace, ?_⟩
  ext x
  exact isEmptyElim x


theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiber_card_le_one_of_isEmptySlots
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    [IsEmpty (LPReplicaOrbitCommonSlot G sites q)]
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
      G sites i j q u).card <= 1 := by
  classical
  rw [Finset.card_le_one]
  intro z hz w hw
  apply lpReplicaOffdiagDecoratedSource_eq_of_crossTrace_eq_of_isEmptySlots
    G sites i j q
  exact (Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hw).2.symm


theorem lpReplicaOffdiagCrossTraceFiber_card_of_isEmptySlots_of_target_nonempty
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    [IsEmpty (LPReplicaOrbitCommonSlot G sites q)]
    (u : LPReplicaOrbitFourColorSlotState G sites q)
    (htarget : (lpReplicaOffdiagBalancedOutputCrossTraceFiber
      G sites i j q u).Nonempty) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
        G sites i j q u).card <=
      (lpReplicaOffdiagBalancedOutputCrossTraceFiber
        G sites i j q u).card := by
  exact (lpReplicaOffdiagDecoratedSourceCrossTraceFiber_card_le_one_of_isEmptySlots
    G sites i j q u).trans (Finset.Nonempty.card_pos htarget)


theorem lpReplicaOffdiagCrossToggleMaskNeighbors_eq_crossTraceFiber
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    lpReplicaOffdiagCrossToggleMaskNeighbors G sites i j q z =
      lpReplicaOffdiagBalancedOutputCrossTraceFiber G sites i j q
        (lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z) := by
  classical
  ext y
  simp [lpReplicaOffdiagCrossToggleMaskNeighbors,
    lpReplicaOffdiagBalancedOutputCrossTraceFiber,
    lpReplicaOffdiagCrossToggleMaskRelated_iff_crossTrace]


theorem lpReplicaOffdiagDecoratedSource_card_eq_sum_crossTraceFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (U : Finset (LPReplicaOrbitFourColorSlotState G sites q))
    (hU : forall z : LPReplicaOffdiagDecoratedSource G sites i j q,
      lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z ∈ U) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) =
      ∑ u ∈ U,
        (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
          G sites i j q u).card := by
  classical
  rw [← Finset.card_univ]
  simpa only [lpReplicaOffdiagDecoratedSourceCrossTraceFiber] using
    Finset.card_eq_sum_card_fiberwise (s :=
      (Finset.univ : Finset
        (LPReplicaOffdiagDecoratedSource G sites i j q)))
      (t := U) (f :=
        lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q) (by
          intro z _
          exact hU z)


theorem lpReplicaOffdiagBalancedOutputs_card_eq_sum_crossTraceFibers
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (U : Finset (LPReplicaOrbitFourColorSlotState G sites q))
    (hU : forall y,
      y ∈ lpReplicaOffdiagBalancedOutputs G sites i j q ->
      lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q y ∈ U) :
    (lpReplicaOffdiagBalancedOutputs G sites i j q).card =
      ∑ u ∈ U,
        (lpReplicaOffdiagBalancedOutputCrossTraceFiber
          G sites i j q u).card := by
  classical
  simpa only [lpReplicaOffdiagBalancedOutputCrossTraceFiber] using
    Finset.card_eq_sum_card_fiberwise
      (s := lpReplicaOffdiagBalancedOutputs G sites i j q)
      (t := U) (f :=
        lpReplicaOffdiagDecoratedTargetCrossTrace G sites i j q) hU


theorem lpReplicaOffdiagCrossToggleMaskHall_of_crossTraceFiberCards
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : forall u : LPReplicaOrbitFourColorSlotState G sites q,
      (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
          G sites i j q u).card <=
        (lpReplicaOffdiagBalancedOutputCrossTraceFiber
          G sites i j q u).card) :
    LPReplicaOffdiagCrossToggleMaskHall G sites i j q := by
  classical
  unfold LPReplicaOffdiagCrossToggleMaskHall
  intro S
  let trace := lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q
  let U := S.image trace
  have hpartition : S.card =
      ∑ u ∈ U, (S.filter fun z => trace z = u).card := by
    simpa only [U] using Finset.card_eq_sum_card_fiberwise
      (s := S) (t := U) (f := trace) (by
        intro z hz
        exact Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  have hdisj : ∀ u, u ∈ U -> ∀ v, v ∈ U -> u ≠ v ->
      Disjoint
        (lpReplicaOffdiagBalancedOutputCrossTraceFiber
          G sites i j q u)
        (lpReplicaOffdiagBalancedOutputCrossTraceFiber
          G sites i j q v) := by
    intro u _ v _ huv
    rw [Finset.disjoint_left]
    intro y hyu hyv
    have hu := (Finset.mem_filter.mp hyu).2
    have hv := (Finset.mem_filter.mp hyv).2
    exact huv (hu.symm.trans hv)
  calc
    S.card = ∑ u ∈ U, (S.filter fun z => trace z = u).card := hpartition
    _ <= ∑ u ∈ U,
        (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
          G sites i j q u).card := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.card_le_card
      intro z hz
      rw [Finset.mem_filter] at hz
      simp only [lpReplicaOffdiagDecoratedSourceCrossTraceFiber,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact hz.2
    _ <= ∑ u ∈ U,
        (lpReplicaOffdiagBalancedOutputCrossTraceFiber
          G sites i j q u).card := by
      exact Finset.sum_le_sum fun u _ => hcard u
    _ = (U.biUnion
        (lpReplicaOffdiagBalancedOutputCrossTraceFiber
          G sites i j q)).card :=
      (Finset.card_biUnion hdisj).symm
    _ <= (S.biUnion
        (lpReplicaOffdiagCrossToggleMaskNeighbors
          G sites i j q)).card := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨u, huU, hyu⟩ := Finset.mem_biUnion.mp hy
      obtain ⟨z, hzS, hzu⟩ := Finset.mem_image.mp huU
      apply Finset.mem_biUnion.mpr
      refine ⟨z, hzS, ?_⟩
      rw [lpReplicaOffdiagCrossToggleMaskNeighbors_eq_crossTraceFiber]
      change lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z = u
        at hzu
      rw [hzu]
      exact hyu


theorem lpReplicaOffdiagCrossTraceFiberCards_of_maskHall
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hHall : LPReplicaOffdiagCrossToggleMaskHall G sites i j q)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
        G sites i j q u).card <=
      (lpReplicaOffdiagBalancedOutputCrossTraceFiber
        G sites i j q u).card := by
  classical
  let sourceFiber := lpReplicaOffdiagDecoratedSourceCrossTraceFiber
    G sites i j q u
  let targetFiber := lpReplicaOffdiagBalancedOutputCrossTraceFiber
    G sites i j q u
  by_cases hsource : sourceFiber.Nonempty
  · have hunion : sourceFiber.biUnion
        (lpReplicaOffdiagCrossToggleMaskNeighbors G sites i j q) =
        targetFiber := by
      ext y
      constructor
      · intro hy
        obtain ⟨z, hz, hyz⟩ := Finset.mem_biUnion.mp hy
        rw [lpReplicaOffdiagCrossToggleMaskNeighbors_eq_crossTraceFiber]
          at hyz
        have hzu :
            lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z = u :=
          (Finset.mem_filter.mp hz).2
        simpa only [hzu, targetFiber] using hyz
      · intro hy
        obtain ⟨z, hz⟩ := hsource
        apply Finset.mem_biUnion.mpr
        refine ⟨z, hz, ?_⟩
        rw [lpReplicaOffdiagCrossToggleMaskNeighbors_eq_crossTraceFiber]
        have hzu :
            lpReplicaOffdiagDecoratedSourceCrossTrace G sites i j q z = u :=
          (Finset.mem_filter.mp hz).2
        simpa only [hzu, targetFiber] using hy
    have h := hHall sourceFiber
    simpa only [sourceFiber, targetFiber, hunion] using h
  · have hempty : sourceFiber = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsource
    simp [sourceFiber, hempty]


theorem lpReplicaOffdiagCrossToggleMaskHall_iff_crossTraceFiberCards
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaOffdiagCrossToggleMaskHall G sites i j q ↔
      forall u : LPReplicaOrbitFourColorSlotState G sites q,
        (lpReplicaOffdiagDecoratedSourceCrossTraceFiber
            G sites i j q u).card <=
          (lpReplicaOffdiagBalancedOutputCrossTraceFiber
            G sites i j q u).card := by
  constructor
  · intro hHall u
    exact lpReplicaOffdiagCrossTraceFiberCards_of_maskHall
      G sites i j q hHall u
  · exact lpReplicaOffdiagCrossToggleMaskHall_of_crossTraceFiberCards
      G sites i j q


end
end StatMech.Ising
