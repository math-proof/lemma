module
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
public import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
public import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots
open Finset
open scoped symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

def lpReplicaFourColorTransport
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (E : α ≃ β) (color : ↑(Finset.univ : Finset α) -> Fin 4) :
    ↑(Finset.univ : Finset β) -> Fin 4 :=
  fun x => color ⟨E.symm x.1, Finset.mem_univ _⟩


end
end StatMech.Ising
