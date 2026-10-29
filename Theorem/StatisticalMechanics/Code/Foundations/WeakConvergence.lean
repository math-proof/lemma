/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/WeakConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Foundations.WeakConvergence
open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal


namespace StatMech

variable {E : Type*} [Countable E]


theorem weakConvergesTo_iff_forall_integral_tendsto
    (μ : ℕ → ProbabilityMeasure (ConfigSpace E)) (ν : ProbabilityMeasure (ConfigSpace E)) :
    WeakConvergesTo μ ν ↔
      ∀ f : (ConfigSpace E) →ᵇ ℝ,
        Tendsto (fun n => ∫ x, f x ∂(μ n : Measure (ConfigSpace E))) atTop
          (𝓝 (∫ x, f x ∂(ν : Measure (ConfigSpace E)))) :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto


theorem weakConvergesTo_iff_forall_lintegral_tendsto
    (μ : ℕ → ProbabilityMeasure (ConfigSpace E)) (ν : ProbabilityMeasure (ConfigSpace E)) :
    WeakConvergesTo μ ν ↔
      ∀ f : (ConfigSpace E) →ᵇ NNReal,
        Tendsto (fun n => ∫⁻ x, f x ∂(μ n : Measure (ConfigSpace E))) atTop
          (𝓝 (∫⁻ x, f x ∂(ν : Measure (ConfigSpace E)))) :=
  ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto


theorem WeakConvergesTo.tendsto_integral
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {ν : ProbabilityMeasure (ConfigSpace E)}
    (h : WeakConvergesTo μ ν) (f : (ConfigSpace E) →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, f x ∂(μ n : Measure (ConfigSpace E))) atTop
      (𝓝 (∫ x, f x ∂(ν : Measure (ConfigSpace E)))) :=
  (weakConvergesTo_iff_forall_integral_tendsto μ ν).1 h f


theorem weakConvergesTo_of_forall_tendsto_integral
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {ν : ProbabilityMeasure (ConfigSpace E)}
    (h : ∀ f : (ConfigSpace E) →ᵇ ℝ,
        Tendsto (fun n => ∫ x, f x ∂(μ n : Measure (ConfigSpace E))) atTop
          (𝓝 (∫ x, f x ∂(ν : Measure (ConfigSpace E))))) :
    WeakConvergesTo μ ν :=
  (weakConvergesTo_iff_forall_integral_tendsto μ ν).2 h

end StatMech
