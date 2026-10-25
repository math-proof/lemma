/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part7
open scoped UpperHalfPlane NNReal
open MeasureTheory ProbabilityTheory Complex Filter Topology


namespace StatMech.SLE

structure IsStandardBrownianMotion {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ → Ω → ℝ) (P : Measure Ω) : Prop where
  
  start : ∀ᵐ ω ∂P, B 0 ω = 0
  
  continuous_paths : ∀ᵐ ω ∂P, Continuous fun t => B t ω
  
  measurable : ∀ t, Measurable (B t)
  
  gaussian : IsGaussianProcess (fun t ω => B t ω) P
  

  increment_law : ∀ s t : ℝ, s ≤ t →
    HasLaw (fun ω => B t ω - B s ω) (gaussianReal 0 (t - s).toNNReal) P
  
  indep_increments : ∀ s t u v : ℝ, s ≤ t → t ≤ u → u ≤ v →
    IndepFun (fun ω => B t ω - B s ω) (fun ω => B v ω - B u ω) P


end StatMech.SLE
