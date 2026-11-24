module
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFour
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber.Part4
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitMultiplicityClass
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutMatching.Part4
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

instance lpReplicaRankFiveDecidableAdj
    (G : SimpleGraph V) (sites : I -> V) :
    DecidableRel (lpReplicaCurrentGraph G sites).Adj :=
  Classical.decRel _


end
end StatMech.Ising
