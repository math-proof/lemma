module
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve3.Part4
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressLib.Part2
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve2.Part2
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerEndpointProve.Part3
public import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerIterationClose
open Finset MeasureTheory
open scoped NNReal FinsetFamily


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


noncomputable def rit_wHalf : Fin 1 → Bool → ℝ := fun _ _ => 1 / 2

end StatMech
