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
import Instance.StatisticalMechanics.Code.FK.PottsClusterSumWiredWeakLimitIdentification.Part3
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


namespace Wired

open IsingFK

variable (bdry : V -> Prop) [DecidablePred bdry]


theorem uniformOfFintype_map_equiv
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    [Nonempty alpha] [Nonempty beta] (e : alpha ≃ beta) :
    (PMF.uniformOfFintype alpha).map e = PMF.uniformOfFintype beta := by
  classical
  ext b
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp [Fintype.card_congr e]
  · intro a hne
    rw [if_neg]
    intro heq
    apply hne
    apply e.injective
    simpa using heq.symm


end Wired
end StatMech.FK
