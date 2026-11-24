module
public import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
public import Theorem.StatisticalMechanics.Code.FrontierB.CurrentMixingErgodicity.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenHomogeneity.Part3
public import Theorem.StatisticalMechanics.Code.FrontierB.CurrentLimitTranslation
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentLimitTranslation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open Ising Lattice Sharpness


noncomputable def currentShiftPattern {E H X : Type*} [Group H] [MulAction H E]
    [DecidableEq E] (g : H) (S : Finset E) (a : ↑S -> X) :
    ↑(currentShiftFinset g S) -> X :=
  fun e => a (currentShiftFinsetEquiv g S e)

end StatMech.FrontierB
