/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
open Set Finset Filter Topology


namespace StatMech

namespace Lattice

noncomputable def boxSV_boxF (d n : ℕ) : Finset (Site d) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(n : ℤ)) n)

end Lattice
end StatMech
