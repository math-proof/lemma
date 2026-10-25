/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilitySkeleton.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.TailBoundSkeleton.Part2
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace TailSummability

variable {α : Type*}


variable [DecidableEq α]


structure FiniteSupportCertificate (α : Type*) [DecidableEq α] where
  support : Finset α
  finitePrefix : Finset α
  finitePrefix_subset_support : finitePrefix ⊆ support
  weight : α → ℝ
  envelope : α → ℝ
  tailBound : ℝ
  zero_off_support : ∀ a, a ∉ support → weight a = 0
  weight_nonneg : ∀ a, 0 ≤ weight a
  envelope_nonneg_on_tail : ∀ a, a ∈ support → a ∉ finitePrefix → 0 ≤ envelope a
  weight_le_envelope_on_tail :
    ∀ a, a ∈ support → a ∉ finitePrefix → weight a ≤ envelope a
  envelope_tail_sum_le :
    (∑ a ∈ support \ finitePrefix, envelope a) ≤ tailBound

end TailSummability
end Exact3D
end StatMech
