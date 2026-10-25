/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part3


namespace StatMech.Onsager

open BigOperators StatMech.Ising

def ons_xSeamPortEdge (L : ℕ) (y : ZMod L) :
    Sym2 (ZMod L × ZMod L) :=
  ons_portEdge L (((-1 : ZMod L), y), 0)

def ons_ySeamPortEdge (L : ℕ) (x : ZMod L) :
    Sym2 (ZMod L × ZMod L) :=
  ons_portEdge L ((x, (-1 : ZMod L)), 1)

end StatMech.Onsager
