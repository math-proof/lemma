/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part5
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaOrbitProfileCoordEquivCommonSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    LPReplicaOrbitProfileCopyCoord G sites m ≃
      LPReplicaOrbitCommonSlot G sites q := by
  classical
  let E := lpReplicaCurrentEdgeOrbitCoordEquiv G sites
  let F : (↑(lpReplicaCurrentEdgeOrbitFixed G sites) ⊕
      (↑(lpReplicaCurrentEdgeOrbitStrictReps G sites) ⊕
        ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites))) -> Type :=
    fun c => Fin (m (E.symm c))
  let outer := Equiv.sumSigmaDistrib F
  let inner := Equiv.sumSigmaDistrib
    (fun c : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites) ⊕
        ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites) => F (Sum.inr c))
  let distribute := outer.trans (Equiv.sumCongr (Equiv.refl _) inner)
  let FixedCoord := Σ e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites),
    F (Sum.inl e)
  let LeftCoord := Σ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
    F (Sum.inr (Sum.inl e))
  let RightCoord := Σ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
    F (Sum.inr (Sum.inr e))
  let PairedCoord := Σ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
    F (Sum.inr (Sum.inl e)) ⊕ F (Sum.inr (Sum.inr e))
  let FixedSlot := Σ e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites),
    Fin (q e.1 / 2)
  let StrictSlot := Σ e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites),
    Fin (q e.1)
  let regroup : FixedCoord ⊕ (LeftCoord ⊕ RightCoord) ≃
      FixedCoord ⊕ PairedCoord := Equiv.sumCongr (Equiv.refl FixedCoord)
    (Equiv.sigmaSumDistrib
      (fun e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites) =>
        F (Sum.inr (Sum.inl e)))
      (fun e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites) =>
        F (Sum.inr (Sum.inr e)))).symm
  let fixedSlots : FixedCoord ≃ FixedSlot :=
    Equiv.sigmaCongrRight fun e :
      ↑(lpReplicaCurrentEdgeOrbitFixed G sites) =>
    Equiv.cast (congrArg Fin
      (lpReplicaProfile_eq_half_of_fixed G sites q m hm e))
  let pairedSlots : PairedCoord ≃ StrictSlot :=
    Equiv.sigmaCongrRight fun e :
      ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites) =>
    lpReplicaProfileOrbitPairedCoordEquivSlot G sites q m hm L e
  exact distribute.trans regroup |>.trans
    (Equiv.sumCongr fixedSlots pairedSlots)


noncomputable def lpReplicaProfileCopyEquivCommonSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (L : LPReplicaProfileOrbitLabel G sites q m) :
    StatMech.Sharpness.FluxEdgeCopy.Copy
        (lpReplicaCurrentGraph G sites) m ≃
      LPReplicaOrbitCommonSlot G sites q :=
  (lpReplicaProfileCopyEquivOrbitCoord G sites m).trans
    (lpReplicaOrbitProfileCoordEquivCommonSlot G sites q m hm L)

end
end StatMech.Ising
