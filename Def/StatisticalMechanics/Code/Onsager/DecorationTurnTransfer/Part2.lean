/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationTurnTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveWinding.Part3
import Theorem.StatisticalMechanics.Code.Onsager.DecorationTurnTransfer


namespace StatMech.Onsager

open StatMech.Onsager.BaseCase

open BigOperators

def ons_walkExpandedDirections
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) : List (Fin 4) :=
  (ons_decExpandedDartList L p).map (fun a ↦ a.2)

def ons_walkExternalDirections
    {L : ℕ} {u v : ons_Dart L}
  (p : (ons_decGraph L).Walk u v) : List (Fin 4) :=
  (ons_decWalkExternalDarts p).map (fun a ↦ a.2)

end StatMech.Onsager
