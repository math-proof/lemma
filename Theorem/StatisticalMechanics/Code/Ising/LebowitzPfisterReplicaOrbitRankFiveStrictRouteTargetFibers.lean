/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteTargetFibers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteCandidateTargets.Part4
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteTargetFibers


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOrbitFourColorSlotEnds_reflectRowToggle_singleton
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (s : LPReplicaOrbitFourColorSlotState G sites q)
    (row : Finset (LPReplicaOrbitCommonSlot G sites q))
    (d x : LPReplicaOrbitCommonSlot G sites q)
    (hd : exists e, d = Sum.inr e) :
    lpReplicaOrbitFourColorSlotEnds G sites q
        (lpReplicaOrbitFourColorSlotReflectRowToggle G sites q {d} row s) x =
      if x = d then
        Sym2.map lpReplicaCurrentReflect
          (lpReplicaOrbitFourColorSlotEnds G sites q s x)
      else lpReplicaOrbitFourColorSlotEnds G sites q s x := by
  classical
  rcases hd with ⟨⟨de, dk⟩, rfl⟩
  rcases x with fixed | ⟨se, sk⟩
  · simp [lpReplicaOrbitFourColorSlotEnds,
      lpReplicaOrbitFourColorSlotReflectRowToggle,
      lpReplicaOrbitFourColorSlotRowToggle,
      lpReplicaOrbitFourColorSlotReflect,
      lpReplicaOrbitFourColorSlotEdge]
  · unfold lpReplicaOrbitFourColorSlotEnds
    change
      (lpReplicaOrbitFourColorSlotEdge G sites q
        (lpReplicaOrbitFourColorSlotReflect G sites q {Sum.inr ⟨de, dk⟩} s)
        (Sum.inr ⟨se, sk⟩)).1 = _
    rw [lpReplicaOrbitFourColorSlotEdge_reflect_strict]
    by_cases h : (Sum.inr ⟨se, sk⟩ :
        LPReplicaOrbitCommonSlot G sites q) = Sum.inr ⟨de, dk⟩
    · have hsd : (⟨se, sk⟩ :
          Σ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites), Fin (q e.1)) =
            ⟨de, dk⟩ := Sum.inr.inj h
      cases hsd
      have hmem : (Sum.inr ⟨de, dk⟩ :
          LPReplicaOrbitCommonSlot G sites q) ∈
          ({Sum.inr ⟨de, dk⟩} :
            Finset (LPReplicaOrbitCommonSlot G sites q)) :=
        Finset.mem_singleton_self _
      rw [if_pos hmem]
      split
      · exact lpReplicaCurrentEdgeReflect_val G sites _
      · rename_i hne
        exact False.elim (hne rfl)
    · have hnmem : (Sum.inr ⟨se, sk⟩ :
          LPReplicaOrbitCommonSlot G sites q) ∉
          ({Sum.inr ⟨de, dk⟩} :
            Finset (LPReplicaOrbitCommonSlot G sites q)) := by
        intro hmem
        exact h (Finset.mem_singleton.mp hmem)
      rw [if_neg hnmem]
      split
      · rename_i heq
        exact False.elim (h heq)
      · rfl


end
end StatMech.Ising
