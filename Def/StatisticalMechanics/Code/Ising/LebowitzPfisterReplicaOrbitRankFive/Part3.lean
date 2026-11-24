module
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFour
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber.Part4
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitMultiplicityClass
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutMatching.Part4
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFive.Part3
open Finset
open scoped symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFive.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedOrSaturatedRankFive
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (u : LPReplicaOrbitFourColorSlotState G sites q) :
    Finset (LPReplicaOffdiagDecoratedSource G sites i j q) := by
  classical
  exact lpReplicaOffdiagDecoratedSourceCrossTraceFiberErasedRankFive
      G sites i j q u ∪
    lpReplicaOffdiagDecoratedSourceCrossTraceFiberSaturatedRankFive
      G sites i j q u


end
end StatMech.Ising
