/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
open MeasureTheory Filter Topology
open scoped BigOperators


namespace StatMech.FrontierB

open Ising Lattice Sharpness


abbrev freeDomainVertices {d : Nat} (K : Finset (Site d)) :=
  {x : Site d // x ∈ K}

end StatMech.FrontierB
