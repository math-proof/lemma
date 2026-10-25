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


namespace StatMech.FrontierA

open scoped BigOperators

open Finset

open StatMech.Onsager

open StatMech.Onsager.BaseCase


def kwRectilinearVector (d : Fin 4) : ℂ :=
  (stepOf d).1 + (stepOf d).2 * Complex.I

end StatMech.FrontierA
