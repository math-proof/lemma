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
public import Structure.StatisticalMechanics.Code.SLE.Cardy.Part2
open scoped UpperHalfPlane NNReal
open Complex Filter Topology

public section

namespace StatMech.SLE

lemma IsCLE.kappa_pos {Ω : Type*} [MeasurableSpace Ω]
    {κ : ℝ} {loops : Ω → Set (Set ℂ)} {μ : MeasureTheory.Measure Ω}
    (h : IsCLE κ loops μ) : 0 < κ :=
  h.param.pos

end StatMech.SLE
