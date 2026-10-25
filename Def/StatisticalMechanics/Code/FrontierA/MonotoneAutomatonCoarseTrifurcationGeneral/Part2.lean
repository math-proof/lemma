/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcationGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseProbabilityGeneral.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonFiniteMerge.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc117mergeproof.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonCoarseTrifurcationGeneral.Part2
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

open StatMech.Walls

variable {d : ℕ}


def SiteThreeMeetBoxGeneral (d n : ℕ) : Set (ConfigSpace (Site d)) :=
  siteToBond ⁻¹' threeMeetBox d n


end StatMech.FrontierA
