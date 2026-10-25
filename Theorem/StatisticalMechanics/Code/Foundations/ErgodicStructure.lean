/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ErgodicStructure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.BirkhoffPointwise.Part4
open MeasureTheory Filter Function MeasurableSpace
open scoped Topology ENNReal


namespace StatMech

namespace ErgodicStructure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {f : α → ℝ}


theorem measurable_invariants_of_comp_eq (hf : Measurable f) (hcomp : f ∘ T = f) :
    Measurable[MeasurableSpace.invariants T] f := by
  rw [MeasurableSpace.measurable_invariants_dom]
  refine ⟨hf, fun s _ => ?_⟩
  rw [hcomp]


theorem condExp_invariants_self [IsFiniteMeasure μ]
    (hf : StronglyMeasurable[MeasurableSpace.invariants T] f) (hfi : Integrable f μ) :
    μ[f | MeasurableSpace.invariants T] = f := by
  have hm : MeasurableSpace.invariants T ≤ ‹MeasurableSpace α› := MeasurableSpace.invariants_le T
  have hsf : SigmaFinite (μ.trim hm) := by
    have : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
    infer_instance
  exact condExp_of_stronglyMeasurable hm hf hfi


theorem condExp_of_comp_eq [IsFiniteMeasure μ]
    (hf : Measurable f) (hfi : Integrable f μ) (hcomp : f ∘ T = f) :
    μ[f | MeasurableSpace.invariants T] = f :=
  condExp_invariants_self (measurable_invariants_of_comp_eq hf hcomp).stronglyMeasurable hfi


theorem tendsto_birkhoffAverage_self_ae [IsProbabilityMeasure μ]
    (hT : MeasurePreserving T μ μ) (hf : Measurable f) (hfi : Integrable f μ)
    (hcomp : f ∘ T = f) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (f x)) := by
  filter_upwards [StatMech.BirkhoffAE.tendsto_birkhoffAverage_condExp_ae hT hfi] with x hx
  rwa [condExp_of_comp_eq hf hfi hcomp] at hx


end ErgodicStructure
end StatMech
