/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLabelTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms.Part5
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaProfileOrbitSlotMove_involutive
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Involutive (lpReplicaProfileOrbitSlotMove G sites q) := by
  intro s
  cases s with
  | mk allocation selectedRep selectedReflect hrep hreflect =>
      apply LPReplicaProfileOrbitSlotState.ext
      · funext e
        ext x
        have hR := hrep e
        have hT := hreflect e
        simp only [lpReplicaProfileOrbitSlotMove, Finset.mem_union,
          Finset.mem_sdiff]
        constructor
        · rintro ((⟨(hx | hx), hnT⟩) | hxR)
          · exact hx.1
          · exact False.elim (hnT hx)
          · exact hR hxR
        · intro hx
          by_cases hxR : x ∈ selectedRep e
          · exact Or.inr hxR
          · left
            refine ⟨Or.inl ⟨hx, hxR⟩, ?_⟩
            intro hxT
            exact (Finset.mem_sdiff.mp (hT hxT)).2 hx
      · rfl
      · rfl


end
end StatMech.Ising
