/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourSubsetCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Ising (crossEdges contourLen connClusterFamily bondFinsetTouch)

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


def RealisedContourWalkEncoding (d n ℓ : ℕ) : Prop :=
  ∃ anchors : Finset (Site d), anchors.card ≤ ℓ ∧
    ∃ (enc : Finset (Sym2 (Site d)) → Σ v : Site d, (hypercubicLattice d).Walk v v)
      (decode : (Σ v : Site d, (hypercubicLattice d).Walk v v) → Finset (Sym2 (Site d))),
      ∀ F ∈ realisedContours d n ℓ,
        (enc F).1 ∈ anchors ∧ (enc F).2.length = ℓ ∧ decode (enc F) = F


end Lattice
end StatMech
