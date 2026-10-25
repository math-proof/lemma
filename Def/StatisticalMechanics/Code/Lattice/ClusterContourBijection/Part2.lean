/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterContourBijection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part2
open Set Finset


namespace StatMech

namespace Lattice

open StatMech.Ising

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


noncomputable def ccb_contourFiber (d n ℓ : ℕ) : Finset (Finset (Site d)) :=
  (connClusterFamily (d := d) n).filter
    (fun (K : Finset (Site d)) => contourLen (↑K) (bondFinsetTouch d n) = ℓ)


end Lattice
end StatMech
