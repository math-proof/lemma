module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part6
public import Theorem.StatisticalMechanics.Code.OSSS.GrandCoupling.Part3
public import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
public import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
public import Theorem.StatisticalMechanics.Code.OSSS.CovLowerBound
public import Theorem.StatisticalMechanics.Code.Walls.oc2_codinglawsingle
open scoped BigOperators ENNReal
open Finset MeasureTheory
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_thetamatch.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.Coding StatMech.OSSS.GrandCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]


def oc2_ExpectAsCubeAt (ν : E → Bool → ℝ) (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n → E) (f : ConfigSpace E → ℝ) : Prop :=
  expect ν f = ∫ u, f (codeMap μ σ u) ∂(Vcube n)


end Walls
end StatMech
