/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part17
import Def.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler


namespace StatMech.Universality

open Finset

noncomputable section

noncomputable instance isingLineBoxBoundary_decidable
    (n : Nat) (p : IsingLineBox n) :
    Decidable (isingLineBoxBoundary n p) := Classical.propDecidable _

end
end StatMech.Universality
