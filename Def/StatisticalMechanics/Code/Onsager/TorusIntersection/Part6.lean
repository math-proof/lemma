/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part5


namespace StatMech.Onsager

open BigOperators StatMech.Ising

noncomputable def ons_zeroFluxHorizontal
    {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) : ZMod 2 :=
  ons_horizontalZBit F p +
    if p.2 = 0 then ons_xFlux F (-1) else 0

noncomputable def ons_zeroFluxVertical
    {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) : ZMod 2 :=
  ons_verticalZBit F p +
    if p.1 = 0 then ons_yFlux F (-1) else 0

end StatMech.Onsager
