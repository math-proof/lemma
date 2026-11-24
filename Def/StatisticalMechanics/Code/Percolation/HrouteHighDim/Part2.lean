module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
public import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim
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


noncomputable def hrHD_corridorEdges (j : Fin d) (L : ℕ) : Finset (Sym2 (Site d)) :=
  (Finset.range L).image (fun t : ℕ => s(hrHD_rayPt j (t : ℤ), hrHD_rayPt j ((t : ℤ) + 1)))


end Percolation
end StatMech
