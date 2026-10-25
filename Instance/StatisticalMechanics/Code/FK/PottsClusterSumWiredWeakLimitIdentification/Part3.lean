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
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredWeakLimitIdentification.Part5
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


namespace Wired

open IsingFK

variable (bdry : V -> Prop) [DecidablePred bdry]


noncomputable instance pinnedWiredComponentColoringNonempty
    {q : Nat} (b : Fin q) (omega : ConfigSpace (Sym2 V)) (v0 : V) :
    Nonempty
      {tau : (wiredSub G bdry omega).ConnectedComponent -> Fin q //
        tau ((wiredSub G bdry omega).connectedComponentMk v0) = b} :=
  ⟨⟨fun _ => b, rfl⟩⟩

end Wired
end StatMech.FK
