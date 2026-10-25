/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoHighChargeSpliceHallRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeLoopHallRouting.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullMaskSpliceKey.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexResolvedCrossRoutedKey.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap.Part7
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoHighChargeSpliceHallRouting.Part3


namespace StatMech.FrontierD

noncomputable section

open Finset

structure SixVertexHorizontalDegreeTwoLoopSynchronizedSingleTargets
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (grade : Nat × Nat) where
  single : ∀ source : SixVertexHorizontalDegreeTwoLoopHighChargeSources
      T middle hmiddle_pos hmiddle_lt grade,
    SixVertexDegreeTwoSynchronizedSupportedSplitTarget
      (sixVertexHorizontalDegreeTwoLoopHighChargeSeed source)
  layers_ne : ∀ source,
    let key := sixVertexHorizontalDegreeTwoLoopSynchronizedSingleSpliceKey
      T middle hmiddle_pos hmiddle_lt grade single source
    key.splice.target false ≠ key.splice.target true
  base_injective : Function.Injective (fun source =>
    sixVertexHorizontalDegreeTwoLoopSpliceTarget source.1
      (sixVertexHorizontalDegreeTwoLoopSynchronizedSingleSpliceKey
        T middle hmiddle_pos hmiddle_lt grade single source))

end
end StatMech.FrontierD
