module
public import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTranslatedBoundary.Part6
public import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredTruncationLimit.Part2
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumWiredComparison.Part3
open Filter MeasureTheory Set Topology
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWiredComparison.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK

open Lattice Percolation

noncomputable section

noncomputable def pottsClusterSumSpinProbabilityMeasure
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
    ProbabilityMeasure (PottsConfig d q) :=
  (pottsClusterFactorInputProbabilityMeasure edgeMeasure).map
    (measurable_pottsClusterSumSpin boundaryColor).aemeasurable

end
end StatMech.FK
