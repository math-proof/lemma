/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part6


namespace StatMech.Onsager

open BigOperators StatMech.Ising

noncomputable def ons_zeroFluxPotential
    {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) : ZMod 2 :=
  ons_zmodPrefix (fun y ↦ ons_zeroFluxHorizontal F (0, y)) p.2 +
    ons_zmodPrefix (fun x ↦ ons_zeroFluxVertical F (x, p.2)) p.1

end StatMech.Onsager
