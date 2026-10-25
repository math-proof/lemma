/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection


namespace StatMech.Onsager

open BigOperators StatMech.Ising

noncomputable def ons_edgeCycleIntersection
    {L : ℕ} [NeZero L]
    (F G : Finset (Sym2 (ZMod L × ZMod L))) : Fin 2 :=
  ∑ p : ZMod L × ZMod L,
    (ons_horizontalBit F p *
        ons_verticalBit G (p.1, p.2 - 1) +
      ons_verticalBit F p *
        ons_horizontalBit G (p.1 - 1, p.2))

end StatMech.Onsager
