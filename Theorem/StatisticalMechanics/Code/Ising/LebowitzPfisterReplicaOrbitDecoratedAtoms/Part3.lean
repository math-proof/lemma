/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitDecoratedAtoms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAtoms.Part3
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms.Part3
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem card_lpReplicaProfileOrbitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaProfileOrbitLabel G sites q m) =
      lpReplicaProfileOrbitMultiplicity G sites q m := by
  classical
  unfold LPReplicaProfileOrbitLabel lpReplicaProfileOrbitMultiplicity
  calc
    _ = ∏ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
        Fintype.card
          ↑((Finset.univ : Finset (Fin (q e.1))).powersetCard (m e.1)) :=
      Fintype.card_pi
    _ = _ := by
      rw [<- Finset.prod_attach
        (lpReplicaCurrentEdgeOrbitStrictReps G sites)]
      apply Finset.prod_congr rfl
      intro e he
      rw [Fintype.card_coe, Finset.card_powersetCard]
      simp


end
end StatMech.Ising
