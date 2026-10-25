/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsAnchorEncode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.ContourSubsetCount
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


def PerContourDualCircuit (d n ℓ : ℕ) : Prop :=
  ∃ anchorPool : Finset (Site d), anchorPool.card ≤ ℓ ∧
    ∃ decode : (Σ v : Site d, (hypercubicLattice d).Walk v v) → Finset (Sym2 (Site d)),
      ∀ F ∈ realisedContours d n ℓ,
        ∃ v : Site d, v ∈ anchorPool ∧
          ∃ W : (hypercubicLattice d).Walk v v, W.length = ℓ ∧ decode ⟨v, W⟩ = F


end Lattice
end StatMech
