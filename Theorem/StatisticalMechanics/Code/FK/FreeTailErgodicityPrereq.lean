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
import Def.StatisticalMechanics.Code.FK.FreeTailErgodicityPrereq
open MeasureTheory Set


namespace StatMech

namespace FK

open ConfigSpace Lattice

variable {d : ℕ}


theorem fkTailEdgeWindow_mono : Monotone (fkTailEdgeWindow d) := by
  intro m n hmn e he x hx
  exact box_mono d hmn (he x hx)

end FK
end StatMech
