/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kingman.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.Kingman
open MeasureTheory Filter Topology


namespace StatMech

namespace Kingman

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}


structure SubadditiveCocycle (T : α → α) (μ : Measure α) (X : ℕ → α → ℝ) : Prop where
  
  measurePreserving : MeasurePreserving T μ μ
  
  integrable : ∀ n, Integrable (X n) μ
  
  subadditive : ∀ m n, ∀ᵐ x ∂μ, X (m + n) x ≤ X m x + X n (T^[m] x)

end Kingman
end StatMech
