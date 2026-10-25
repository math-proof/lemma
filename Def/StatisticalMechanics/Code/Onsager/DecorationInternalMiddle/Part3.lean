/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalMiddle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationInternalEndpoint
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Theorem.StatisticalMechanics.Code.Onsager.DecorationInternalMiddle.Part2


namespace StatMech.Onsager

open Matrix BigOperators


noncomputable def ons_decMiddleAugmented
    (L : ℕ) (decWeight : ons_DecEdge L → ℂ)
    (omega u v t : ℂ) (site : ZMod L × ZMod L) :
    Matrix (ons_Dart L ⊕ Fin 2) (ons_Dart L ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks
    (ons_KWmatDecorationWeightedPhase L
      (ons_scaleDecEdgeWeight decWeight
        (ons_decChainEdge site 1) 0) omega u v)
    (ons_decMiddleU L decWeight omega site)
    (t • ons_decMiddleV L decWeight omega u v site)
    0


end StatMech.Onsager
