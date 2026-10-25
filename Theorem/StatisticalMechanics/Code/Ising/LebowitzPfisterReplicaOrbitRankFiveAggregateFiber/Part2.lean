/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFive.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateFiber.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive_card_le_three
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
      G sites i j q u).card ≤ 3 := by
  classical
  let inactivePair := fun z : LPReplicaOffdiagDecoratedSource G sites i j q =>
    Finset.univ \ lpReplicaOrbitFourColorSlotRowMask G sites q
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)
  calc
    (lpReplicaOffdiagDecoratedSourceCrossTraceFiberLowRowRankFive
        G sites i j q u).card ≤
      (lpReplicaEligibleInactivePairs
        (lpReplicaOrbitFourColorSlotEdge G sites q u)).card := by
      apply Finset.card_le_card_of_injOn inactivePair
      · intro z hz
        have hz' := (Finset.mem_filter.mp hz)
        have htrace := (Finset.mem_filter.mp hz'.1).2
        simpa only [inactivePair, htrace] using
          (lpReplicaOffdiagDecoratedSource_rank_five_lowRow_inactivePair_mem_eligible
            G sites hsite hij q hcard z hz'.2)
      · intro z hz w hw hpairs
        have hz' := (Finset.mem_filter.mp hz)
        have hw' := (Finset.mem_filter.mp hw)
        apply lpReplicaOffdiagDecoratedSourceRowMask_injOn_crossTraceFiber
          G sites i j q u hz'.1 hw'.1
        exact (sdiff_right_inj (Finset.subset_univ _)
          (Finset.subset_univ _)).mp hpairs
    _ ≤ 3 := lpReplicaEligibleInactivePairs_card_le_three _


theorem lpReplicaOffdiagDecoratedSource_rank_five_highRow_rowMask_eq_univ
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hhigh : LPReplicaOffdiagDecoratedSource.IsHighRowRankFive
      G sites i j q z) :
    lpReplicaOrbitFourColorSlotRowMask G sites q
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z) =
      Finset.univ := by
  classical
  rcases hhigh with hsat | hhigh
  · exact lpReplicaOffdiagDecoratedSource_rank_five_saturated_rowMask_eq_univ
      G sites hsite hij q hcard z hsat
  · let d := lpReplicaDecoratedSourceRowGateData G sites i j q z
    let K := lpReplicaCurrentCopies G sites z.1.1.1 d.1 true false
    let C := Finset.univ \ K
    change K.card = 3 /\ exists c, c ∈ C /\ (d.1 c).1 = true at hhigh
    obtain ⟨hthree, c, hcC, hcrow⟩ := hhigh
    have hconst : ∀ a ∈ C, d.1 a = d.1 c := by
      intro a ha
      exact lpReplicaOffdiagDecoratedSource_rank_five_complement_tag_constant
        G sites hsite hij q hcard z hthree a ha c hcC
    have hall (a) : (d.1 a).1 = true := by
      by_cases haK : a ∈ K
      · have hatag : d.1 a = (true, false) := by
          simpa only [K, lpReplicaCurrentCopies, Finset.mem_filter,
            Finset.mem_univ, true_and] using haK
        simp [hatag]
      · have haC : a ∈ C := Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, haK⟩
        exact congrArg Prod.fst (hconst a haC) |>.trans hcrow
    ext x
    simp only [lpReplicaOrbitFourColorSlotRowMask, Finset.mem_filter,
      Finset.mem_univ, true_and]
    let e := (lpReplicaProfileCopyEquivCommonSlot G sites q z.1.1.1
      z.1.1.2 z.2.2).symm x
    have he := hall e
    have htag := lpReplicaOffdiagDecoratedSource_orientedTag_eq_rowGateData
      G sites i j q z
    have he' := congrFun htag e
    simpa only [lpReplicaOffdiagDecoratedSourceSlotState,
      lpReplicaOrientedFourColorSlotState,
      lpReplicaOrbitFourColorSlotStateOfTag, Equiv.apply_symm_apply,
      Equiv.symm_apply_apply, iff_true] using
        (congrArg Prod.fst he').trans he


end
end StatMech.Ising
