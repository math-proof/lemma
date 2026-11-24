module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
public import Def.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Percolation

variable {d : ℕ}


abbrev hrHD_RouteIdx (d : ℕ) := Finset (Sym2 (Site d)) × Site d × Site d × Site d


end Percolation
end StatMech
