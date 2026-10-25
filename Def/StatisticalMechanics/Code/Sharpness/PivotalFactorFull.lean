/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
open MeasureTheory Function Set
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


def internalEdges (S : Set (Site d)) : Set (Sym2 (Site d)) :=
  {e | ∃ x ∈ S, ∃ y ∈ S, e = s(x, y)}

end Sharpness
end StatMech
