/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/Cardy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
public import Theorem.StatisticalMechanics.Code.SLE.Cardy.Part7
public section

open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

structure IsCLE {Ω : Type*} [MeasurableSpace Ω]
    (κ : ℝ) (loops : Ω → Set (Set ℂ)) (μ : MeasureTheory.Measure Ω) : Prop where
  
  param : IsCLEParameter κ
  

  measurable : ∀ S : Set ℂ, MeasurableSet {ω | S ∈ loops ω}
  

  isProbability : MeasureTheory.IsProbabilityMeasure μ


end StatMech.SLE
