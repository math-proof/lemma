module
public import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityLimits
public import Theorem.StatisticalMechanics.Code.FrontierB.BoxCurrentPatternFactor.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentMeasures
public import Def.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open Sharpness Ising Lattice

theorem currentParityMarginalPMF_toMeasure {E : Type*} [Countable E]
    [DecidableEq E]
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E)) (S : Finset E) :
    (currentParityMarginalPMF mu S).toMeasure =
      (((currentMarginal mu S).map
        (Measurable.of_discrete (f := currentLocalParity)).aemeasurable :
          ProbabilityMeasure (↑S → Bool)) : Measure (↑S → Bool)) := by
  exact Measure.toPMF_toMeasure _

end StatMech.FrontierB
