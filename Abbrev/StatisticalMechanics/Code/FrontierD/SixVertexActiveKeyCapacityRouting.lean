/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyCapacityRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteKeyCapacityMatching.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting
open Finset


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexHorizontalActualDeficitFineUnionKeyFiber
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) (key : SixVertexPairFineUnionKey T) :=
  {source : SixVertexHorizontalActualDeficitTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle //
    sixVertexHorizontalActualDeficitFineUnionKey source = key}

abbrev SixVertexHorizontalActualSurplusFineUnionKeyFiber
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) (key : SixVertexPairFineUnionKey T) :=
  {target : SixVertexHorizontalActualSurplusTokens T grade
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle //
    sixVertexHorizontalActualSurplusFineUnionKey target = key}


end
end StatMech.FrontierD
