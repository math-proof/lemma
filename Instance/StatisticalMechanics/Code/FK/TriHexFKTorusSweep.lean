/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
import Theorem.StatisticalMechanics.Code.FK.ActiveEdges.Part4
import Theorem.StatisticalMechanics.Code.Universality.STTTransport.Part3
import Def.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part8


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


noncomputable instance hexagonalTorusIsolatedCenterFintype
    (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    Fintype (HexagonalTorusIsolatedCenter L omega) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

end StatMech.FK.PeriodicPlanar
