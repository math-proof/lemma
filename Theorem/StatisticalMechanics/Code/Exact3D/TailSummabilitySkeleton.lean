/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.TailBoundSkeleton.Part2
import Mathlib.Topology.Algebra.InfiniteSum.Basic
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace TailSummability

variable {α : Type*}


theorem sum_nonneg_on {s : Finset α} {f : α → ℝ}
    (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    0 ≤ ∑ a ∈ s, f a :=
  Finset.sum_nonneg fun a ha => hf a ha

variable [DecidableEq α]


theorem sum_eq_prefix_add_tail {s front : Finset α} (hfront : front ⊆ s)
    (f : α → ℝ) :
    (∑ a ∈ s, f a) =
      (∑ a ∈ front, f a) + ∑ a ∈ s \ front, f a := by
  calc
    (∑ a ∈ s, f a) =
        (∑ a ∈ s \ front, f a) + ∑ a ∈ front, f a :=
      (Finset.sum_sdiff hfront).symm
    _ = (∑ a ∈ front, f a) + ∑ a ∈ s \ front, f a := by
      rw [add_comm]


theorem tail_sum_nonneg {s front : Finset α} {f : α → ℝ}
    (hf : ∀ a, a ∈ s → a ∉ front → 0 ≤ f a) :
    0 ≤ ∑ a ∈ s \ front, f a := by
  exact Finset.sum_nonneg fun a ha => by
    have htail : a ∈ s ∧ a ∉ front := by
      simpa using ha
    exact hf a htail.1 htail.2


theorem tail_sum_le_envelope_sum {s front : Finset α}
    {f envelope : α → ℝ}
    (henv : ∀ a, a ∈ s → a ∉ front → f a ≤ envelope a) :
    (∑ a ∈ s \ front, f a) ≤ ∑ a ∈ s \ front, envelope a := by
  exact Finset.sum_le_sum fun a ha => by
    have htail : a ∈ s ∧ a ∉ front := by
      simpa using ha
    exact henv a htail.1 htail.2


end TailSummability
end Exact3D
end StatMech
