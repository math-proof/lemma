module
public import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
public import Theorem.StatisticalMechanics.Code.OSSS.Poincare.Part2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Theorem.StatisticalMechanics.Code.Probability.KKLInequality.Part2
open scoped BigOperators
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLInequality.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Probability

open StatMech.OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def maxInfl [Nonempty E] (ν : E → Bool → ℝ) (g : ConfigSpace E → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (OSSS.infl ν g)


end Probability
end StatMech
