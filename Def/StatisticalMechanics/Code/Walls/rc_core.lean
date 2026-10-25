/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve3.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyClose.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc_dpairsfiberrecursion
import Theorem.StatisticalMechanics.Code.Walls.rc_dpairsmodular
import Theorem.StatisticalMechanics.Code.Walls.rmr_reflectinvolution.Part2
import Theorem.StatisticalMechanics.Code.Walls.rmr_baseanddisjoint
import Theorem.StatisticalMechanics.Code.Walls.rc_core
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech

variable {α : Type*} [DecidableEq α]


def rc_core_CountBoxBridge : Prop :=
  ∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), poc_SlabCard A B


end StatMech.Walls
