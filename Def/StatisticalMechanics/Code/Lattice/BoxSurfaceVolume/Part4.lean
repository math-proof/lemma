/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part3
open Set Finset Filter Topology


namespace StatMech

namespace Lattice

noncomputable def boxSV_edgeF (d n : ℕ) : Finset (Site d × Site d) :=
  ((boxSV_boxF d n) ×ˢ (boxSV_boxF d n)).filter
    (fun p => (∑ i, (p.1 i - p.2 i).natAbs) = 1)

end Lattice
end StatMech
