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
import Theorem.StatisticalMechanics.Code.SLE.CardyCLE.Part4
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

def IsConformallyInvariantLoopLaw {Ω : Type*} [MeasurableSpace Ω]
    (loops : Ω → Set (Set ℂ)) (μ : MeasureTheory.Measure Ω) : Prop :=
  ∀ (m : Mobius ℂ) (relabel : Ω → Ω), Measurable relabel →
    (∀ ω, loops (relabel ω) = (fun S => m.apply '' S) '' (loops ω)) →
    MeasureTheory.Measure.map relabel μ = μ


end StatMech.SLE
