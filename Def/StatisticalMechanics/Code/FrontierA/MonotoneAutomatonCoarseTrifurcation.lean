/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseProbability.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonFiniteMerge.Part2
import Theorem.StatisticalMechanics.Code.Walls.bkmmerge
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonCoarseTrifurcation
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

open StatMech.Walls


def SiteFaithfulAllOpenTrifAt (n : ℕ) : Set (ConfigSpace (Site 2)) :=
  siteToBond ⁻¹' {omega | FaithfulAllOpenTrifAt omega n 0}

end StatMech.FrontierA
