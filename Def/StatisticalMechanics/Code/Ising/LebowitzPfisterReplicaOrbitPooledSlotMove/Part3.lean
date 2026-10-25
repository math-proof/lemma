/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledSlotMove.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledSlotMove.Part2
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaPooledSelectedSlotMoveEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    LPReplicaPooledSelectedSlotState G sites q ≃
      LPReplicaPooledSelectedSlotState G sites q where
  toFun := lpReplicaPooledSelectedSlotMove G sites q
  invFun := lpReplicaPooledSelectedSlotMove G sites q
  left_inv := lpReplicaPooledSelectedSlotMove_involutive G sites q
  right_inv := lpReplicaPooledSelectedSlotMove_involutive G sites q


noncomputable def lpReplicaPooledSelectedSlotStateOfCopies
    (G : SimpleGraph V) (sites : I -> V)
    (m q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    LPReplicaPooledSelectedSlotState G sites q :=
  lpReplicaPooledSelectedOrbitLabelEquivSlotState G sites q
    ⟨⟨m, hm⟩,
      ⟨⟨StatMech.Sharpness.FluxEdgeCopy.profileFlux
        (lpReplicaCurrentGraph G sites) m P,
          StatMech.Sharpness.FluxEdgeCopy.profileFlux_le
            (lpReplicaCurrentGraph G sites) m P⟩,
        lpReplicaProfileOrbitSelectedLabelOfCopies
          G sites q m hm P L⟩⟩

end
end StatMech.Ising
