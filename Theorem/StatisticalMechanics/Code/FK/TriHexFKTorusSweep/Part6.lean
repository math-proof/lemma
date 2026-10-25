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
import Def.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part6


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


theorem starFKRepresentativeDirection_open_of_open
    (config : LocalConfig) (i : Fin 3)
    (hi : triHexLocalDirection config i = true) :
    triHexLocalDirection config (starFKRepresentativeDirection config) = true := by
  rcases config with ⟨b0, b1, b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases i <;>
    simp_all [triHexLocalDirection, starFKRepresentativeDirection]


end StatMech.FK.PeriodicPlanar
