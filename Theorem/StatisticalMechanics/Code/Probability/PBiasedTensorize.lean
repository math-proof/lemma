module
public import Theorem.StatisticalMechanics.Code.Probability.PBiasedConvexity.Part2
public import Theorem.StatisticalMechanics.Code.Probability.KKLpBiased.Part2
public import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
public import Def.StatisticalMechanics.Code.Probability.PBiasedTensorize
open scoped BigOperators
open Finset
open Real
set_option linter.style.longLine false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


@[simp] theorem ptn_val_true : ptn_val true = 1 := rfl

@[simp] theorem ptn_val_false : ptn_val false = 0 := rfl


end StatMech.Probability
