/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimFiniteVolumeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.OneDimTransferPerron
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part2
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


def chainBond (z : ℤ) : Sym2 (Site 1) := s(site1 z, site1 (z + 1))

end StatMech.FrontierB
