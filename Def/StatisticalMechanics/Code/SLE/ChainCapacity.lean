/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerCapacity
import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Theorem.StatisticalMechanics.Code.SLE.ChainCapacity.Part2
open Complex Set Filter Topology MeasureTheory
open scoped NNReal


namespace StatMech.SLE

noncomputable def loewnerChain_of_sle_realization {Ω : Type*} (κ : ℝ)
    (B : ℝ → Ω → ℝ) (ω : Ω) (g : ℝ → ℂ → ℂ)
    (hcont : Continuous fun t => B t ω)
    (hloe : SatisfiesLoewnerEquation (sleDriving κ B ω) g) : LoewnerChain where
  driving := sleDriving κ B ω
  driving_continuous := continuous_sleDriving κ B ω hcont
  maps := g
  loewner := hloe

end StatMech.SLE
