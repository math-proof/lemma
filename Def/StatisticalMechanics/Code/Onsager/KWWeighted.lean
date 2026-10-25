/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWWeighted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.KWPhaseLoops
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part13


namespace StatMech.Onsager

open Matrix BigOperators

noncomputable def ons_KWmatWeighted (L : ℕ)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (omega : ℂ) :
    Matrix (ons_Dart L) (ons_Dart L) ℂ :=
  fun d2 d1 =>
    if d2.1 = ons_dirStep L d1.2 d1.1 then
      weight (ons_portEdge L d1) * ons_turnW omega d1.2 d2.2
    else 0

end StatMech.Onsager
