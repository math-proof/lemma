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
import Def.StatisticalMechanics.Code.Onsager.TorusDecoration.Part6


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

@[simp] theorem ons_decEdgeBit_mk {L : ℕ} (P : ons_PortPattern L)
    (d e : ons_Dart L) :
    ons_decEdgeBit P s(d, e) = ons_decNeighborBit P d e := rfl

end StatMech.Onsager
