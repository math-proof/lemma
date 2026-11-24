module
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledGateSplit
public import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part3
public import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber.Part2
open Finset
open scoped symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def LPReplicaAggregateDecoratedTarget
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Fin 2 × Sigma fun i : I => Sigma fun j : I =>
    LPReplicaDecoratedOrbitAtom G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q

end
end StatMech.Ising
