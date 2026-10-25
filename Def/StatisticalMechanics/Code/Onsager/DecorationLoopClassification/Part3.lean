/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopClassification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part7
import Theorem.StatisticalMechanics.Code.Onsager.DecorationLoopClassification.Part3


namespace StatMech.Onsager

open Finset SimpleGraph

noncomputable def ons_decLoopRootFinset
    (L : ℕ) {n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    Finset (ons_Dart L) :=
  Finset.univ.image d ∪
    Finset.univ.image (fun k ↦ ons_dartRev L (d k))

end StatMech.Onsager
