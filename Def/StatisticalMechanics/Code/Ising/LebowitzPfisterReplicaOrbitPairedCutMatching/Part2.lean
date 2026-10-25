/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSequentialExchange.Part5
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutMatching
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaOffdiagCoupledPairedNeighbors
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact Finset.univ.filter fun y =>
    LPReplicaOffdiagCoupledPairedMatch G sites i j q z y

noncomputable def lpReplicaOffdiagCoupledPairedOutputs
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact Finset.univ.filter
    (LPReplicaOffdiagCoupledPairedOutput G sites i j q)

noncomputable def lpReplicaOffdiagCoupledPairedOutputsAtProfile
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset (LPReplicaOffdiagDecoratedTarget G sites i j q) := by
  classical
  exact (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).filter fun y =>
    lpReplicaOffdiagDecoratedTargetProfile G sites i j q y = m


noncomputable def lpReplicaOffdiagCoupledPairedRelevantProfiles
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Finset ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) := by
  classical
  exact ((Finset.univ : Finset
      (LPReplicaOffdiagDecoratedSource G sites i j q)).image
        (fun z => z.1.1.1)) ∪
    (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).image
      (lpReplicaOffdiagDecoratedTargetProfile G sites i j q)

end
end StatMech.Ising
