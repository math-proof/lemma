/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Lemma2417.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic
import Structure.v1.Atlas.ArithmeticGeometry.code.Lemma2417


noncomputable section

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

namespace Lemma2417

/-- Three points $(x_1, z_1), (x_2, z_2), (x_3, z_3) \in \mathbb{Z}_p^2$ are collinear if they
lie on a common line $z = \alpha x + \beta$ for some $\alpha, \beta \in \mathbb{Z}_p$. -/
def AreCollinear (x₁ z₁ x₂ z₂ x₃ z₃ : ℤ_[p]) : Prop :=
  ∃ α β : ℤ_[p], z₁ = α * x₁ + β ∧ z₂ = α * x₂ + β ∧ z₃ = α * x₃ + β

end Lemma2417
end
