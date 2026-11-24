module
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
public import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport.Part3
public import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledSlotMove
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledSlotMove.lean -/
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

noncomputable instance instFintypeLPReplicaPooledSelectedOrbitLabel
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaPooledSelectedOrbitLabel G sites q) :=
  Fintype.ofEquiv (LPReplicaPooledSelectedSlotState G sites q)
    (lpReplicaPooledSelectedOrbitLabelEquivSlotState G sites q).symm


end
end StatMech.Ising
