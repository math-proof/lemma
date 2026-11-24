module
public import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFinite.Part5
public import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
public import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneNat
open scoped BigOperators
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneNat.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


omit [Fintype E] [DecidableEq E] in

theorem natUpperLevel_isIncreasing {F : ConfigSpace E -> ℕ} (hF : Monotone F) (k : ℕ) :
    IsIncreasing (natUpperLevel F k) := by
  intro omega eta homega hlevel
  exact lt_of_lt_of_le hlevel (hF homega)


end StatMech.FrontierA
