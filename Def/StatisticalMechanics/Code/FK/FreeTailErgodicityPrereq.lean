/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeTailErgodicityPrereq.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Foundations.AeTailInvariant.Part4
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
open MeasureTheory Set


namespace StatMech

namespace FK

open ConfigSpace Lattice

variable {d : ℕ}


def fkTailEdgeWindow (d n : ℕ) : Set (Sym2 (Site d)) :=
  {e | ∀ x, x ∈ e → x ∈ box d n}

end FK
end StatMech
