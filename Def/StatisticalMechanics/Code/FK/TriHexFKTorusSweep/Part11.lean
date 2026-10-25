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
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part10


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


def triHexDirectionOdds (y0 y1 y2 : ℝ) (i : Fin 3) : ℝ :=
  ![y0, y1, y2] i


def starFKIsolatedCenterFactor (q : ℝ) (config : LocalConfig) : ℝ :=
  if config = (false, false, false) then q else 1

end StatMech.FK.PeriodicPlanar
