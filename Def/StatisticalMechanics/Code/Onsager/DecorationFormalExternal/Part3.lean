/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSurgery.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part2


namespace StatMech.Onsager

open BigOperators Finset

def ons_decIsFirstReturnLoop
    {L n : ℕ} [NeZero n] (d : ons_Dart L)
    (loop : Fin n → ons_Dart L) : Prop :=
  loop 0 = d ∧
    (∀ k, k ≠ 0 → loop k ≠ d) ∧
      ∀ k, loop k ≠ ons_dartRev L d

end StatMech.Onsager
