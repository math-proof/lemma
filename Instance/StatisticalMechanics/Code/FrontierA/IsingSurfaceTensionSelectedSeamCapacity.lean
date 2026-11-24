module
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLowRankSwitching.Part2
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAggregateMatching.Part7
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismGinibre.Part7
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionInteriorBlockClosure
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCriticalInfiniteVolumeReduction
open Finset
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSelectedSeamCapacity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

instance selectedSeamCapacityDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


end
end StatMech.FrontierA
