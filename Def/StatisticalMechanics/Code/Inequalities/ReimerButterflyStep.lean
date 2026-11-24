module
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled2
public import Mathlib.Data.Finset.Prod
open Finset
open scoped FinsetFamily


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyStep.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

variable {α : Type*} [DecidableEq α]


def dpairsCount (𝒜 ℬ : Finset (Finset α)) : ℕ :=
  ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card


end StatMech
