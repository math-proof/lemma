/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredWeakLimitIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification.Part6
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.FK.FreeDLRExtreme
import Instance.StatisticalMechanics.Code.FK.PottsClusterSumWiredWeakLimitIdentification
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


namespace Wired

open IsingFK

variable (bdry : V -> Prop) [DecidablePred bdry]


noncomputable def compatibleBoundarySpinEquivPinnedWiredComponents
    {q : Nat} (b : Fin q) (omega : ConfigSpace (Sym2 V))
    (v0 : V) (hv0 : bdry v0) :
    CompatibleBoundarySpin G bdry b omega ≃
      {tau : (wiredSub G bdry omega).ConnectedComponent -> Fin q //
        tau ((wiredSub G bdry omega).connectedComponentMk v0) = b} := by
  let E : ((wiredSub G bdry omega).ConnectedComponent -> Fin q) ≃
      {sigma : V -> Fin q // ConstOnWired G bdry omega sigma} :=
    constOnWiredEquiv G bdry omega
  refine (Equiv.subtypeEquivRight (fun sigma =>
    constOnOpen_boundaryFixed_iff G bdry b omega sigma)).trans ?_
  refine (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans ?_
  refine (E.subtypeEquiv ?_).symm
  intro tau
  show tau ((wiredSub G bdry omega).connectedComponentMk v0) = b ↔
    BoundaryFixed bdry b (E tau).1
  constructor
  · intro h x hx
    show tau ((wiredSub G bdry omega).connectedComponentMk x) = b
    rw [wiredSub_componentMk_eq_of_bdry G bdry hx hv0]
    exact h
  · intro h
    simpa [E, constOnWiredEquiv] using h v0 hv0

end Wired
end StatMech.FK
