/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part7
import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopClassification.Part4


namespace StatMech.Onsager

open Finset SimpleGraph

def ons_decLoopOrientation
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    Fin n ⊕ Fin n → (Fin n → ons_Dart L)
  | Sum.inl k => ons_rotate k d
  | Sum.inr k => ons_rotate k (ons_loopRev L d)

end StatMech.Onsager
