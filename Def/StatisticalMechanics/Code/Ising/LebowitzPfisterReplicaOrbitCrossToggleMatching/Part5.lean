/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part21
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part6
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part4
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaDecoratedSourceCanonicalHalfSlotMask
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    Finset (LPReplicaOrbitCommonSlot G sites q) :=
  lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1 z.1.1.2 z.2.2
    (lpReplicaDecoratedSourceCanonicalHalfSelector
      G sites i j q z).selector


noncomputable def lpReplicaDecoratedSourceCanonicalHalfBranchBit
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) : Bool :=
  match lpReplicaDecoratedSourceCanonicalHalfBranch
      G sites hsite hij q z with
  | Sum.inl _ => false
  | Sum.inr _ => true


noncomputable def lpReplicaDecoratedSourceCanonicalHalfCandidate
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    Bool × LPReplicaOrbitFourColorSlotState G sites q :=
  (lpReplicaDecoratedSourceCanonicalHalfBranchBit
      G sites hsite hij q z,
    lpReplicaOrbitFourColorSlotCrossToggle G sites q
      (lpReplicaDecoratedSourceCanonicalHalfSlotMask G sites i j q z)
      (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z))


end
end StatMech.Ising
