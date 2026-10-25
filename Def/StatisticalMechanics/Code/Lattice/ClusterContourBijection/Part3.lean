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
import Theorem.StatisticalMechanics.Code.Lattice.ClusterContourBijection.Part3
open Set Finset


namespace StatMech

namespace Lattice

open StatMech.Ising

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


def ccb_ContourEncodingExists (d n ℓ : ℕ) : Prop :=
  ∃ anchors : Finset (Site d),
    anchors.card ≤ ℓ ∧
    ∃ enc : Finset (Site d) → Σ v : Site d, (hypercubicLattice d).Walk v v,
      (∀ K ∈ ccb_contourFiber d n ℓ, (enc K).1 ∈ anchors ∧ (enc K).2.length = ℓ) ∧
      Set.InjOn enc (↑(ccb_contourFiber d n ℓ))


end Lattice
end StatMech
