/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part8
open scoped UpperHalfPlane NNReal
open MeasureTheory ProbabilityTheory Complex Filter Topology


namespace StatMech.SLE

structure IsChordalSLE {Ω : Type*} [MeasurableSpace Ω]
    (κ : ℝ) (B : ℝ → Ω → ℝ) (P : Measure Ω)
    (D : Ω → ℝ → Set ℂ) (g : Ω → ℝ → ℂ → ℂ) : Prop where
  
  kappa_nonneg : 0 ≤ κ
  
  isBrownian : IsStandardBrownianMotion B P
  

  loewner : ∀ᵐ ω ∂P, SatisfiesMaximalLoewnerEquation
    (sleDriving κ B ω) (D ω) (g ω)


end StatMech.SLE
