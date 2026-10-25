/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/RussoHamming.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.RussoInfluence.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.Hamming
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.BeffaraDC.RussoHamming


namespace StatMech

namespace BeffaraDC

open ConfigSpace Function Finset

variable {E : Type*} [Fintype E] [DecidableEq E]


def numOpen (ω : ConfigSpace E) : ℕ := (univ.filter (fun e => ω e = true)).card

end BeffaraDC
end StatMech
