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
import Theorem.StatisticalMechanics.Code.Onsager.TorusDecoration.Part5


namespace StatMech.Onsager

open Finset SimpleGraph

open StatMech.Ising

def ons_decEdgeBit {L : ℕ} (P : ons_PortPattern L) :
    Sym2 (ons_Dart L) → Fin 2 :=
  Sym2.lift ⟨ons_decNeighborBit P, ons_decNeighborBit_symm P⟩

end StatMech.Onsager
