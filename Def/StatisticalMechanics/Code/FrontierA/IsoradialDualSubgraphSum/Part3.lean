/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualSubgraphSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Lean.Elab.Tactic.Omega
public import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialDualSubgraphSum.Part2

@[expose] public section

namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {E K : Type*} [Fintype E] [DecidableEq E]


def kwDualSubgraphSum [CommSemiring K]
    (coefficient : Finset E -> K) (weight : E -> K) : K :=
  ∑ F : Finset E, coefficient F * ∏ e ∈ F, weight e

end StatMech.FrontierA
