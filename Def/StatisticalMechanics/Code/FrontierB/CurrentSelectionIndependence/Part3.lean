/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentSelectionIndependence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.CurrentParityLimits
import Theorem.StatisticalMechanics.Code.FrontierB.BoxCurrentPatternFactor.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentMeasures
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part2
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice

noncomputable def latticeEdgePart (d : ℕ)
    (S : Finset (Sym2 (Site d))) : Finset (Sym2 (Site d)) :=
  S.filter fun e => e ∈ (hypercubicLattice d).edgeSet

end StatMech.FrontierB
