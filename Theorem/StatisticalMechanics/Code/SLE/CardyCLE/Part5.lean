/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
import Theorem.StatisticalMechanics.Code.SLE.Cardy.Part8
import Def.StatisticalMechanics.Code.SLE.CardyCLE.Part5
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

lemma idLoopLaw_invariant_under_id {Ω : Type*} [MeasurableSpace Ω]
    (loops : Ω → Set (Set ℂ)) (μ : MeasureTheory.Measure Ω) :
    Measurable (id : Ω → Ω) ∧
      (∀ ω, loops (id ω) = (fun S => (Mobius.id ℂ).apply '' S) '' (loops ω)) →
      MeasureTheory.Measure.map id μ = μ := by
  rintro ⟨_, _⟩
  simp

end StatMech.SLE
