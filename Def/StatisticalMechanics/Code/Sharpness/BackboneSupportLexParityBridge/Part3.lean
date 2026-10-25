/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexParityBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexCounterexample.Part2
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part2
open Finset


namespace StatMech.Sharpness

noncomputable def shbParitySeriesMassOn
    {E : Type*} [DecidableEq E] (S : Finset E)
    (P : Finset E → Prop) [DecidablePred P] (x : ℝ) : ℝ :=
  ∑ A ∈ S.powerset,
    if P A then
      ∏ e ∈ S, if e ∈ A then shbOddCurrentSeries x else shbEvenCurrentSeries x
    else 0


def shbParityPolynomialOn
    {E : Type*} [DecidableEq E] (S : Finset E)
    (P : Finset E → Prop) [DecidablePred P] (t : ℝ) : ℝ :=
  ∑ A ∈ S.powerset, if P A then t ^ A.card else 0


end StatMech.Sharpness
