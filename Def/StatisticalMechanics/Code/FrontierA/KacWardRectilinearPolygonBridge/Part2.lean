/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearPolygonBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonJordanEquivalence
import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge


namespace StatMech.FrontierA

open scoped BigOperators

open Finset

open StatMech.Onsager

open StatMech.Onsager.BaseCase


noncomputable def kwRectilinearAngle (d : Fin 4) : Real.Angle :=
  match d with
  | 0 => 0
  | 1 => (Real.pi / 2 : ℝ)
  | 2 => (Real.pi : ℝ)
  | 3 => (-(Real.pi / 2) : ℝ)

end StatMech.FrontierA
