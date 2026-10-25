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
import Theorem.StatisticalMechanics.Code.FK.FreeTailErgodicityPrereq.Part2
open MeasureTheory Set


namespace StatMech

namespace FK

open ConfigSpace Lattice

variable {d : ℕ}


abbrev FKIsTailEvent (d : ℕ)
    (s : Set (ConfigSpace (Sym2 (Site d)))) : Prop :=
  AtiTailEvent (fkTailEdgeWindow d) s


end FK
end StatMech
