/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalExternal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSurgery.Part2
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3


namespace StatMech.Onsager

open BigOperators Finset

instance ons_decIsFirstReturnLoop_decidable
    {L n : ℕ} [NeZero n] (d : ons_Dart L)
    (loop : Fin n → ons_Dart L) :
    Decidable (ons_decIsFirstReturnLoop d loop) := by
  unfold ons_decIsFirstReturnLoop
  infer_instance

end StatMech.Onsager
