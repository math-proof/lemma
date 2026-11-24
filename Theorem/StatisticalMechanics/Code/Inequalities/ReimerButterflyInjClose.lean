module
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubleCoverClose.Part4
public import Def.StatisticalMechanics.Code.Inequalities.ReimerButterflyInjClose
open Finset
open scoped FinsetFamily


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyInjClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

open ConfigSpace


@[simp] lemma rbi_cfg_zero (a b : Bool) : rbi_cfg a b 0 = a := rfl

@[simp] lemma rbi_cfg_one (a b : Bool) : rbi_cfg a b 1 = b := rfl


end StatMech
