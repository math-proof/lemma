/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.DctSurfacePartition.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Percolation.Sharpness.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2
open MeasureTheory Function Set SimpleGraph Filter
open scoped NNReal ENNReal Topology
open StatMech


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


noncomputable def crossPoly (d n : ℕ) (t : ℝ) : ℝ :=
  prob t ((boxEdgeFinset d (n + 1)).restrict '' (boxCrossingEvent d (n + 1)))


end Percolation
end StatMech
