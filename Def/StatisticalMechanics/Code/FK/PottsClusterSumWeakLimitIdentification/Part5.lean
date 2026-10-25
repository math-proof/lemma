/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumContinuity.Part2
import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part8
import Theorem.StatisticalMechanics.Code.FrontierB.FreeInfiniteMultipointES
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification.Part4
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def freeESJointFiniteMeasure
    (d n q : Nat) [NeZero q] {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : Real)) :
    ProbabilityMeasure (PottsJointConfig d q) :=
  ⟨(ivp_freeJointPMF (boxGraph d n) q hp hp1 hq).toMeasure.map
      (ivp_extendJoint d n q),
    inferInstance⟩


noncomputable def boxClusterSumJointFactor
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (n : Nat)
    (input : ConfigSpace (Sym2 (boxVerts d n)) × (Site d -> Fin q)) :
    (boxVerts d n -> Fin q) × ConfigSpace (Sym2 (boxVerts d n)) :=
  ((fun x => pottsClusterSumSpin boundaryColor
      (extendEdge d n input.1) input.2 (x : Site d)), input.1)

end StatMech.FK
