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
import Theorem.StatisticalMechanics.Code.Walls.pc1peierls
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch
  ConnectedContourCount origin)

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


def pc1_ContourInjection (d n ℓ : ℕ) : Prop :=
  ∃ f : Finset (Sym2 (Site d)) → Σ v : Site d, (hypercubicLattice d).Walk v v,
    (∀ F ∈ realisedContours d n ℓ, f F ∈ pc1_axisWalks d ℓ) ∧
      Set.InjOn f (↑(realisedContours d n ℓ))


end Lattice
end StatMech
