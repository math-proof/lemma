/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreePairMixingFromTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FK.FreeTailTriviality
import Theorem.StatisticalMechanics.Code.FK.FKTwoBoxDecoupling.Part2
import Theorem.StatisticalMechanics.Code.Foundations.BirkhoffErgodic
import Theorem.StatisticalMechanics.Code.FK.FreePairMixingFromTail
open MeasureTheory Set Filter Function
open scoped BigOperators ENNReal Topology


namespace StatMech

namespace FK

open ConfigSpace Lattice

variable {d : ℕ}


noncomputable def freeAxisVertexSupport
    (F : Finset (Sym2 (Site d))) : Finset (Site d) :=
  F.biUnion fun e => {e.out.1, e.out.2}

end FK
end StatMech
