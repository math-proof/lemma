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
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWiredWeakLimitIdentification.Part9
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


namespace Wired

open IsingFK

variable (bdry : V -> Prop) [DecidablePred bdry]


theorem clusterColorJointFiniteMeasure_eq_wiredPottsJointFiniteMeasure
    (d n q : Nat) [NeZero q] (hd : 1 ≤ d) (hn : 1 ≤ n)
    (b : Fin q) (beta J : Real)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
    clusterColorJointFiniteMeasure d n q b beta J hp hp1 =
      wiredPottsJointFiniteMeasure d n q b beta J hp.le := by
  obtain ⟨v0, hv0⟩ := IsingFK.boxBoundary_nonempty d n hd hn
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (ivp_extendJoint d n q)
      (clusterColorJointPMF (boxGraph d n) (boxBoundary d n)
        b beta J hp hp1).toMeasure =
    Measure.map (ivp_extendJoint d n q)
      (ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
        b beta J hp.le).toMeasure
  rw [clusterColorJointPMF_eq_ivp_wiredJointPMF
    (boxGraph d n) (boxBoundary d n) b beta J hp hp1 v0 hv0]

end Wired
end StatMech.FK
