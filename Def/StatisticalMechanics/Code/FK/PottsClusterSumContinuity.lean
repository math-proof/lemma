/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumContinuity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumProductErgodicity.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FreeInfiniteParityTopology.Part4
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumContinuity
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation


noncomputable def pottsIIDLabelProbabilityMeasure
    (d q : Nat) [NeZero q] : ProbabilityMeasure (Site d -> Fin q) :=
  ⟨pottsIIDLabelMeasure d q, inferInstance⟩


noncomputable def pottsClusterFactorInputProbabilityMeasure
    {d q : Nat} [NeZero q]
    (edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
    ProbabilityMeasure
      (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :=
  edgeMeasure.prod (pottsIIDLabelProbabilityMeasure d q)


noncomputable def pottsClusterSumJointProbabilityMeasure
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
    ProbabilityMeasure ((Site d -> Fin q) × ConfigSpace (Sym2 (Site d))) :=
  (pottsClusterFactorInputProbabilityMeasure edgeMeasure).map
    (measurable_pottsClusterSumJointFactor boundaryColor).aemeasurable


end StatMech.FK
