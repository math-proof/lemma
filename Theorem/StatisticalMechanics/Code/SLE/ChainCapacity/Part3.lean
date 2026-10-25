/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerCapacity
import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Def.StatisticalMechanics.Code.SLE.ChainCapacity
open Complex Set Filter Topology MeasureTheory
open scoped NNReal


namespace StatMech.SLE

@[simp] lemma loewnerChain_of_sle_realization_maps {Ω : Type*} (κ : ℝ)
    (B : ℝ → Ω → ℝ) (ω : Ω) (g : ℝ → ℂ → ℂ)
    (hcont : Continuous fun t => B t ω)
    (hloe : SatisfiesLoewnerEquation (sleDriving κ B ω) g) :
    (loewnerChain_of_sle_realization κ B ω g hcont hloe).maps = g := rfl

@[simp] lemma loewnerChain_of_sle_realization_driving {Ω : Type*} (κ : ℝ)
    (B : ℝ → Ω → ℝ) (ω : Ω) (g : ℝ → ℂ → ℂ)
    (hcont : Continuous fun t => B t ω)
    (hloe : SatisfiesLoewnerEquation (sleDriving κ B ω) g) :
    (loewnerChain_of_sle_realization κ B ω g hcont hloe).driving = sleDriving κ B ω := rfl


theorem chordalSLE_realization_capacity_parametrized {Ω : Type*} (κ : ℝ)
    (B : ℝ → Ω → ℝ) (ω : Ω) (g : ℝ → ℂ → ℂ)
    (hcont : Continuous fun t => B t ω)
    (hloe : SatisfiesLoewnerEquation (sleDriving κ B ω) g) {a₁ : ℝ → ℝ}
    (hnorm : ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (a₁ t))
    (hrate : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t) :
    ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (2 * t) :=
  loewner_capacity_eq_of_loewnerChain
    (loewnerChain_of_sle_realization κ B ω g hcont hloe) hnorm hrate


end StatMech.SLE
