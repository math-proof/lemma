/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsAnchorEncode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.ContourSubsetCount
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsAnchorEncode.Part3
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


def AxisContourDualCircuit (d n ℓ : ℕ) : Prop :=
  ∃ decode : (Σ v : Site d, (hypercubicLattice d).Walk v v) → Finset (Sym2 (Site d)),
    ∀ F ∈ realisedContours d n ℓ,
      ∃ j : ℕ, j < ℓ ∧
        ∃ W : (hypercubicLattice d).Walk (axisVertex d j) (axisVertex d j),
          W.length = ℓ ∧ decode ⟨axisVertex d j, W⟩ = F


end Lattice
end StatMech
