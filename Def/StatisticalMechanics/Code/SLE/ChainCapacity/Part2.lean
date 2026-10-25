/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/ChainCapacity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerCapacity
import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Theorem.StatisticalMechanics.Code.SLE.ChainCapacity.Part3
open Complex Set Filter Topology MeasureTheory
open scoped NNReal


namespace StatMech.SLE

noncomputable def capacityParametrizedChain_of_sle_realization {Ω : Type*} (κ : ℝ)
    (B : ℝ → Ω → ℝ) (ω : Ω) (g : ℝ → ℂ → ℂ)
    (hcont : Continuous fun t => B t ω)
    (hloe : SatisfiesLoewnerEquation (sleDriving κ B ω) g) {a₁ : ℝ → ℝ}
    (K : ℝ → Set ℂ) (hKhull : ∀ t, IsCompactHull (K t)) (hKmono : Monotone K)
    (hnorm : ∀ t ∈ Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (a₁ t))
    (hrate : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt a₁ 2 (Ici (0 : ℝ)) t) :
    CapacityParametrizedChain where
  chain := loewnerChain_of_sle_realization κ B ω g hcont hloe
  hull := K
  coeff := a₁
  hull_isHull := hKhull
  hull_monotone := hKmono
  capacity := ⟨hnorm, hrate⟩

end StatMech.SLE
