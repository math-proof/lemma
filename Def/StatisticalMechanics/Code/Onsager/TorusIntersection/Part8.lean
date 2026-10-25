/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part7


namespace StatMech.Onsager

open BigOperators StatMech.Ising

noncomputable def ons_edgeCycleZIntersection
    {L : ℕ} [NeZero L]
    (F G : Finset (Sym2 (ZMod L × ZMod L))) : ZMod 2 :=
  ∑ p : ZMod L × ZMod L,
    (ons_horizontalZBit F p *
        ons_verticalZBit G (p.1, p.2 - 1) +
      ons_verticalZBit F p *
        ons_horizontalZBit G (p.1 - 1, p.2))

end StatMech.Onsager
