module
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaComponentReflection.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
public import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCollisionResummation.Part5
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean -/
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

abbrev LPReplicaCollisionCopy
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :=
  Σ e : (lpReplicaCurrentGraph G sites).edgeFinset,
    Fin (a e) ⊕ Fin (b (lpReplicaCurrentEdgeReflect G sites e))


end
end StatMech.Ising
