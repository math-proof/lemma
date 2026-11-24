module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForest
public import Theorem.StatisticalMechanics.Code.Onsager.GeneralUmlaufsatz
public import Mathlib.GroupTheory.Perm.Fin
open scoped BigOperators
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardCycleAssembly.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open Matrix

open StatMech.Onsager StatMech.Onsager.BaseCase StatMech.Onsager.NoDoubleWind
  StatMech.Onsager.GeneralUmlaufsatz


noncomputable def kwWeightedCycleTransition {E : Type*} [Fintype E]
    [DecidableEq E] (sigma : Equiv.Perm E) (weight : E -> ℂ) :
    Matrix E E ℂ :=
  fun i j => if j = sigma i then weight i else 0


end StatMech.FrontierA
