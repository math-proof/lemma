/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift


namespace StatMech.Onsager

open BigOperators StatMech.Ising

def ons_edgeBit {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) (e : Sym2 V) : Fin 2 :=
  if e ∈ F then 1 else 0

def ons_horizontalBit {L : ℕ}
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) : Fin 2 :=
  ons_edgeBit F (ons_portEdge L (p, 0))

def ons_verticalBit {L : ℕ}
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (p : ZMod L × ZMod L) : Fin 2 :=
  ons_edgeBit F (ons_portEdge L (p, 1))

end StatMech.Onsager
