/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/PBiasedTensorize.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.PBiasedConvexity.Part2
import Theorem.StatisticalMechanics.Code.Probability.KKLpBiased.Part2
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
import Theorem.StatisticalMechanics.Code.Probability.PBiasedTensorize.Part8
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


noncomputable def ptn_reindex {κ : Type*} (σ : κ ≃ ι) (f : ConfigSpace ι → ℝ) :
    ConfigSpace κ → ℝ :=
  fun y => f (fun i => y (σ.symm i))


def ptn_cubeEquiv {κ : Type*} (σ : κ ≃ ι) : ConfigSpace ι ≃ ConfigSpace κ :=
  Equiv.arrowCongr σ.symm (Equiv.refl Bool)


end StatMech.Probability
