/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part13
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOrbitFourColorSelectedStrictSlots_commonSlotsOfCopies
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)) :
    lpReplicaOrbitFourColorSelectedStrictSlots G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q m hm L P) e =
      ((lpReplicaProfileOrbitSelectedLabelOfCopies
          G sites q m hm P L).2 e).1.1 ∪
        ((lpReplicaProfileOrbitSelectedLabelOfCopies
          G sites q m hm P L).2 e).2.1 := by
  classical
  ext k
  simp only [lpReplicaOrbitFourColorSelectedStrictSlots,
    Finset.mem_filter, Finset.mem_univ, true_and,
    lpReplicaProfileOrbitSelectedLabelOfCopies,
    lpReplicaCopyIndicesAtEdge, Finset.mem_union, Finset.mem_map]
  let E := lpReplicaProfileCopyEquivCommonSlot G sites q m hm L
  let x : LPReplicaOrbitCommonSlot G sites q := Sum.inr ⟨e, k⟩
  constructor
  · intro hx
    have hc : E.symm x ∈ P :=
      (mem_lpReplicaOrbitCommonSlotsOfCopies_iff
        G sites q m hm L P x).mp hx
    let c := E.symm x
    change c ∈ P at hc
    have hEc : E c = x := E.apply_symm_apply x
    let tag : StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) m -> LPReplicaRowTag :=
      fun _ => (false, false)
    have hedgeCopy := lpReplicaOrbitFourColorSlotEdge_stateOfTag_copy
      G sites q m hm L tag c
    have hedge :
        (if k ∈ (L e).1 then e.1
          else lpReplicaCurrentEdgeReflect G sites e.1) = c.1 := by
      rw [hEc] at hedgeCopy
      simpa only [x, lpReplicaOrbitFourColorSlotEdge,
        lpReplicaOrbitFourColorSlotStateOfTag_allocation] using hedgeCopy
    by_cases hk : k ∈ (L e).1
    · left
      have hcEdge : c.1 = e.1 := by simpa only [if_pos hk] using hedge.symm
      rcases c with ⟨ce, a⟩
      dsimp only at hcEdge
      subst ce
      refine ⟨a, hc, ?_⟩
      dsimp only [E, x] at hEc
      rw [lpReplicaProfileCopyEquivCommonSlot_strict] at hEc
      have hpair := Sum.inr.inj hEc
      exact eq_of_heq (Sigma.mk.inj_iff.mp hpair).2
    · right
      have hcEdge : c.1 = lpReplicaCurrentEdgeReflect G sites e.1 := by
        simpa only [if_neg hk] using hedge.symm
      rcases c with ⟨ce, a⟩
      dsimp only at hcEdge
      subst ce
      refine ⟨a, hc, ?_⟩
      dsimp only [E, x] at hEc
      rw [lpReplicaProfileCopyEquivCommonSlot_reflectStrict] at hEc
      have hpair := Sum.inr.inj hEc
      exact eq_of_heq (Sigma.mk.inj_iff.mp hpair).2
  · rintro (⟨a, ha, hak⟩ | ⟨a, ha, hak⟩)
    · apply (mem_lpReplicaOrbitCommonSlotsOfCopies_iff
        G sites q m hm L P x).mpr
      have hslot : E ⟨e.1, a⟩ = x := by
        dsimp only [E, x]
        rw [lpReplicaProfileCopyEquivCommonSlot_strict, hak]
      rw [← hslot, E.symm_apply_apply]
      exact ha
    · apply (mem_lpReplicaOrbitCommonSlotsOfCopies_iff
        G sites q m hm L P x).mpr
      have hslot : E
          ⟨lpReplicaCurrentEdgeReflect G sites e.1, a⟩ = x := by
        dsimp only [E, x]
        rw [lpReplicaProfileCopyEquivCommonSlot_reflectStrict, hak]
      rw [← hslot, E.symm_apply_apply]
      exact ha


end
end StatMech.Ising
