/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourCount.Part4
import Theorem.StatisticalMechanics.Code.Ising.PeierlsClose
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


def ConnectedContourCount (d n : ℕ) : Prop :=
  ∀ ℓ : ℕ,
    (((connClusterFamily (d := d) n).filter
        (fun (K : Finset (Site d)) => contourLen (↑K) (bondFinsetTouch d n) = ℓ)).card : ℝ)
      ≤ (ℓ : ℝ) * (2 * d : ℝ) ^ ℓ


end Ising
end StatMech
