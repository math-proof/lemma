/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Def.StatisticalMechanics.Code.Sharpness.PivotalFactorFull
open MeasureTheory Function Set
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


theorem mem_internalEdges {S : Set (Site d)} {x y : Site d} (hx : x ∈ S) (hy : y ∈ S) :
    s(x, y) ∈ internalEdges S := ⟨x, hx, y, hy, rfl⟩


end Sharpness
end StatMech
