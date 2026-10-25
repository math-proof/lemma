/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part13
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaOrbitSpatialSelectorOfCopies
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (P : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m)) :
    forall e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
      Finset (Fin (q e.1)) :=
  fun e =>
    ((lpReplicaProfileOrbitSelectedLabelOfCopies
      G sites q m hm P L).2 e).1.1 ∪
    ((lpReplicaProfileOrbitSelectedLabelOfCopies
      G sites q m hm P L).2 e).2.1


def lpReplicaOrbitFourColorSlotReflectFamily
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : forall e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
      Finset (Fin (q e.1)))
    (s : LPReplicaOrbitFourColorSlotState G sites q) :
    LPReplicaOrbitFourColorSlotState G sites q where
  allocation := fun e => s.allocation e ∆ P e
  color := s.color


end
end StatMech.Ising
