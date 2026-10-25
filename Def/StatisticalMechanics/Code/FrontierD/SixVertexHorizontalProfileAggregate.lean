/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileAggregate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalTwoCutSwitch.Part2
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileAggregate
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalCompletionProfile
    (T : EvenTorus) (horizontal : SixVertexHorizontalField T) :
    Option (SixVertexHorizontalCompletionProfile T) :=
  if hcompletion : Nonempty (SixVertexVerticalCompletion T horizontal) then
    some
      { forcedTrue :=
          ⟨(sixVertexHorizontalForcedTrueColumns horizontal).card,
            Nat.lt_succ_of_le (by
              simpa using Finset.card_le_univ
                (sixVertexHorizontalForcedTrueColumns horizontal))⟩
        free :=
          ⟨(sixVertexHorizontalFreeColumns horizontal).card,
            Nat.lt_succ_of_le (by
              simpa using Finset.card_le_univ
                (sixVertexHorizontalFreeColumns horizontal))⟩ }
  else none

def sixVertexHorizontalProfileChooseCount
    {T : EvenTorus} (sector : Fin (T.width + 1)) :
    Option (SixVertexHorizontalCompletionProfile T) -> Nat
  | none => 0
  | some profile =>
      if profile.forcedTrue.val <= sector.val then
        Nat.choose profile.free.val
          (sector.val - profile.forcedTrue.val)
      else 0


end
end StatMech.FrontierD
