module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
public import Abbrev.StatisticalMechanics.Code.Percolation.HrouteHighDim
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


noncomputable def hrHD_routePre (p : hrHD_RouteIdx d) : Set (ConfigSpace (Sym2 (Site d))) :=
  (fun ω => forceOpenFinset p.1 ω) ⁻¹' (NeighborTrifPrecursor d p.2.1 p.2.2.1 p.2.2.2)


end Percolation
end StatMech
