/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualSubgraphSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Ring.Commute
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Lean.Elab.Tactic.Omega
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialDualSubgraphSum.Part2


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {E K : Type*} [Fintype E] [DecidableEq E]


def kwDualSubgraphSum [CommSemiring K]
    (coefficient : Finset E -> K) (weight : E -> K) : K :=
  ∑ F : Finset E, coefficient F * ∏ e ∈ F, weight e

end StatMech.FrontierA
