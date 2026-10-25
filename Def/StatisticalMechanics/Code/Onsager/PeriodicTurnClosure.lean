/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PeriodicTurnClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.TorusPeriodicLift


namespace StatMech.Onsager

open BigOperators

open StatMech.Onsager.BaseCase

def ons_pathDisplacement : List (Fin 4) → ℤ × ℤ
  | [] => 0
  | d :: ds => stepOf d + ons_pathDisplacement ds

def ons_pathVertices : List (Fin 4) → List (ℤ × ℤ)
  | [] => [0]
  | d :: ds => 0 :: (ons_pathVertices ds).map (stepOf d + ·)

def ons_openTurnSum : List (Fin 4) → ℤ
  | [] => 0
  | [_] => 0
  | d :: e :: ds =>
      ons_turnPow d e + ons_openTurnSum (e :: ds)

def ons_cyclicTurnSum : List (Fin 4) → ℤ
  | [] => 0
  | d :: ds =>
      ons_openTurnSum (d :: ds) +
        ons_turnPow (d :: ds).getLast! d

end StatMech.Onsager
