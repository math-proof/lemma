/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummabilityExample.Part4
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailSummabilityExample

open TailSummability

noncomputable section

def singletonFiniteCertificate :
    FiniteSupportCertificate ℕ where
  support := {0}
  finitePrefix := {0}
  finitePrefix_subset_support := by
    intro a ha
    simpa using ha
  weight := fun n => if n = 0 then (3 : ℝ) else 0
  envelope := fun _ => 0
  tailBound := 0
  zero_off_support := by
    intro a ha
    have hne : a ≠ 0 := by
      intro h
      exact ha (by simp [h])
    simp [hne]
  weight_nonneg := by
    intro a
    by_cases h : a = 0 <;> simp [h]
  envelope_nonneg_on_tail := by
    intro _ _ _
    norm_num
  weight_le_envelope_on_tail := by
    intro a hsupport hnotPrefix
    have ha0 : a = 0 := by
      simpa using hsupport
    exact False.elim (hnotPrefix (by simp [ha0]))
  envelope_tail_sum_le := by
    simp


def singletonFiniteAsInfinite :
    InfiniteTailCertificate ℕ :=
  singletonFiniteCertificate.toInfiniteTailCertificate


end
end InfiniteTailSummabilityExample
end Exact3D
end StatMech
