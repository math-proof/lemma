/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InclusionExclusion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.FK.InclusionExclusion.Part3
open StatMech ConfigSpace
open scoped BigOperators Pointwise


namespace StatMech

namespace FK

variable {E : Type*}


section Representatives

variable [DecidableEq E]


noncomputable def repOf (S : Finset E) (φ : ↥S → Bool) : ConfigSpace E :=
  fun e => if h : e ∈ S then φ ⟨e, h⟩ else false


end Representatives
end FK
end StatMech
