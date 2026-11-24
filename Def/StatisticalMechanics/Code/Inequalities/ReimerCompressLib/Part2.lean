module
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve3.Part4
public import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressLib
open Finset MeasureTheory
open scoped NNReal FinsetFamily


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressLib.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

open ConfigSpace

variable {α : Type*} [DecidableEq α]


section Bridge

variable [Fintype α]


def familyEvent (𝒜 : Finset (Finset α)) : Set (ConfigSpace α) := {ω | cfgSupport ω ∈ 𝒜}

end Bridge
end StatMech
