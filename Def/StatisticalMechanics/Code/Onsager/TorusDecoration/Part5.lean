/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.TrivalentCycles
import Theorem.StatisticalMechanics.Code.Onsager.TurningTelescope.Part3
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part4


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

def ons_portChainBit {L : ℕ} (P : ons_PortPattern L)
    (s : ZMod L × ZMod L) : Fin 3 → Fin 2 :=
  ons_decChainCompletion (P.bit (s, 0)) (P.bit (s, 1)) (P.bit (s, 2))


def ons_decNeighborBit {L : ℕ} (P : ons_PortPattern L)
    (d e : ons_Dart L) : Fin 2 :=
  if e = ons_dartRev L d then P.bit d else
    if d.1 = e.1 then
      match d.2, e.2 with
      | 0, 1 | 1, 0 => ons_portChainBit P d.1 0
      | 1, 2 | 2, 1 => ons_portChainBit P d.1 1
      | 2, 3 | 3, 2 => ons_portChainBit P d.1 2
      | _, _ => 0
    else 0

end StatMech.Onsager
