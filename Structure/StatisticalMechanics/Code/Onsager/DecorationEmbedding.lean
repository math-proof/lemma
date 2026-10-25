/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part4


namespace StatMech.Onsager

structure ons_DecMicroPoint (L : ℕ) where
  cell : ZMod L × ZMod L
  offsetX : Fin 8
  offsetY : Fin 8
deriving DecidableEq

end StatMech.Onsager
