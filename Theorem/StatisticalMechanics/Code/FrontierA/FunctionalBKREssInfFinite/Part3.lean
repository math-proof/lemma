/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKREssInfFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralDual.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralFinite
import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Mathlib.MeasureTheory.Function.EssSup
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKREssInfFinite.Part3
open MeasureTheory
open scoped BigOperators ENNReal NNReal


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem functionalDisjointEssMaxAt_eq
    (p : E → NNReal) (hp0 : ∀ e, 0 < p e) (hp1 : ∀ e, p e < 1)
    (f g : ConfigSpace E → ℝ) (omega eta : ConfigSpace E) :
    functionalDisjointEssMaxAt p (fun e => (hp1 e).le) f g omega eta =
      functionalDisjointMaxAt f g omega eta := by
  unfold functionalDisjointEssMaxAt functionalDisjointMaxAt
  apply Finset.sup'_congr (disjointCoordinatePairs_nonempty (E := E)) rfl
  intro pair _
  rw [cylinderEssInf_eq_cylinderMin p hp0 hp1,
    cylinderEssInf_eq_cylinderMin p hp0 hp1]

theorem functionalDisjointEssMax_eq
    (p : E → NNReal) (hp0 : ∀ e, 0 < p e) (hp1 : ∀ e, p e < 1)
    (f g : ConfigSpace E → ℝ) (omega : ConfigSpace E) :
    functionalDisjointEssMax p (fun e => (hp1 e).le) f g omega =
      functionalDisjointMax f g omega :=
  functionalDisjointEssMaxAt_eq p hp0 hp1 f g omega omega


end StatMech.FrontierA
