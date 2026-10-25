/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part2


namespace StatMech.Onsager

open BigOperators StatMech.Ising

def ons_horizontalZBit {L : ℕ}
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) : ZMod 2 :=
  (ons_horizontalBit F p : ZMod 2)

def ons_verticalZBit {L : ℕ}
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) : ZMod 2 :=
  (ons_verticalBit F p : ZMod 2)

noncomputable def ons_xFlux {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L))) (x : ZMod L) : ZMod 2 :=
  ∑ y : ZMod L, ons_horizontalZBit F (x, y)

noncomputable def ons_yFlux {L : ℕ} [NeZero L]
    (F : Finset (Sym2 (ZMod L × ZMod L))) (y : ZMod L) : ZMod 2 :=
  ∑ x : ZMod L, ons_verticalZBit F (x, y)

end StatMech.Onsager
