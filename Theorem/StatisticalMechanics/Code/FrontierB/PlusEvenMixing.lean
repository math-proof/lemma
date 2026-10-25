/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusEvenMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.PairMixingCofinite
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentLimitTranslation.Part3
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
open MeasureTheory Set
open scoped BigOperators


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.ConfigSpace StatMech.FK

theorem siteTranslation_solution_finite {d : Nat} (x y : Site d) :
    {g : Multiplicative (Site d) | g • x = y}.Finite := by
  apply finite_solution_of_injective
  intro z g h hgh
  change Multiplicative.toAdd g + z = Multiplicative.toAdd h + z at hgh
  change Multiplicative.toAdd g = Multiplicative.toAdd h
  exact add_right_cancel hgh

end StatMech.FrontierB
