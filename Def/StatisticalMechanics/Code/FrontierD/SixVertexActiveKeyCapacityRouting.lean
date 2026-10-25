/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexActiveKeyCapacityRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FiniteKeyCapacityMatching.Part3
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexActiveKeyCapacityRouting
open Finset


namespace StatMech.FrontierD

noncomputable section

def SixVertexHorizontalTwoCycleActiveKeyFiberRoutings
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  forall grade, Nonempty
    (SixVertexHorizontalTwoCycleActiveKeyFiberRouting T middle
      hmiddle_pos hmiddle_lt grade)


end
end StatMech.FrontierD
