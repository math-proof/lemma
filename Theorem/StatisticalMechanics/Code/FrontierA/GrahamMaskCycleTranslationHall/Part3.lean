/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskCycleTranslationHall.Part3
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

open StatMech.Sharpness.RandomCurrent


theorem card_leftMaskFiber_le_rightMaskFiber_of_cycleTranslate
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a : leftMaskFiber ends m j k l zero p)
    (q : rightMaskFiber ends m j k l zero p)
    (hgate : ∀ c : leftMaskFiber ends m j k l zero p,
      RowsDisconnect ends m
        (rightMaskCycleTranslate m a.1.1 c.1.1 q.1.1) k zero) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) :=
  Fintype.card_le_of_embedding
    (maskFiberCycleTranslateEmbedding
      ends m j k l zero p a q hgate)


end StatMech.GrahamGHS.FourColor
