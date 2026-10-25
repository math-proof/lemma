/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForest
import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
import Mathlib.GroupTheory.Perm.Fin
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardCycleAssembly
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open Matrix

open StatMech.Onsager StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.GeneralUmlaufsatz


noncomputable def kwTwoOrientationCycleTransition
    {E : Type*} [Fintype E] [DecidableEq E]
    (sigma : Equiv.Perm E) (weight : Bool -> E -> ℂ) :
    Matrix (E × Bool) (E × Bool) ℂ :=
  Matrix.blockDiagonal fun b => kwWeightedCycleTransition sigma (weight b)


end StatMech.FrontierA
