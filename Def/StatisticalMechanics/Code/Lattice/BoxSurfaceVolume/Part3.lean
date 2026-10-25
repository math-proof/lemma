/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part2
open Set Finset Filter Topology


namespace StatMech

namespace Lattice

noncomputable def boxSV_boundaryCard (d n : ℕ) : ℕ :=
  (vertexBoundary_finite d n).toFinset.card


end Lattice
end StatMech
