/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/pc1peierls.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsAnchorEncode.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch
  ConnectedContourCount origin)

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


noncomputable def pc1_axisWalks (d ℓ : ℕ) :
    Finset (Σ v : Site d, (hypercubicLattice d).Walk v v) :=
  (axisAnchorPool d ℓ).sigma (fun v => (hypercubicLattice d).finsetWalkLength ℓ v v)


end Lattice
end StatMech
