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
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge
open Finset


namespace StatMech.Sharpness

noncomputable def shbParitySeriesMass
    {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset E → Prop) [DecidablePred P] (x : ℝ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset E).powerset,
    if P A then
      ∏ e : E, if e ∈ A then shbOddCurrentSeries x else shbEvenCurrentSeries x
    else 0


def shbParityPolynomial
    {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset E → Prop) [DecidablePred P] (t : ℝ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset E).powerset,
    if P A then t ^ A.card else 0

end StatMech.Sharpness
