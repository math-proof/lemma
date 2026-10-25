/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part8
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFivePairedHall.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHighRowComplementToggle.Part6
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaOffdiagRankFiveOutputCollisionClassLow
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (output : LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaOffdiagDecoratedTarget G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact (lpReplicaOffdiagRankFiveOutputCollisionClass
    G sites i j q output y).filter
      (LPReplicaOffdiagDecoratedSource.IsLowRowRankFive G sites i j q)


noncomputable def lpReplicaOffdiagRankFiveOutputCollisionClassHigh
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (output : LPReplicaOffdiagDecoratedSource G sites i j q ->
      LPReplicaOffdiagDecoratedTarget G sites i j q)
    (y : LPReplicaOffdiagDecoratedTarget G sites i j q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact (lpReplicaOffdiagRankFiveOutputCollisionClass
    G sites i j q output y).filter
      (LPReplicaOffdiagDecoratedSource.IsHighRowRankFive G sites i j q)


end
end StatMech.Ising
