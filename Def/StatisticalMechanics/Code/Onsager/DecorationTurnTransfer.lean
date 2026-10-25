/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveWinding.Part3


namespace StatMech.Onsager

open StatMech.Onsager.BaseCase

open BigOperators

def ons_portLineAdj (a b : Fin 4) : Prop :=
  a.val + 1 = b.val ∨ b.val + 1 = a.val

def ons_internalMicroDirections : List (Fin 4) → List (Fin 4)
  | a :: b :: rest =>
      [b, b, a + 2, a + 2] ++ ons_internalMicroDirections (b :: rest)
  | _ => []

end StatMech.Onsager
