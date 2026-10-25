/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohDerived.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.EffaceableUniversal
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.EffaceableUniversal
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohomology
import Theorem.v1.Atlas.AlgebraicGeometryI.code.SheafCohomology.Part2


noncomputable section

open CohomologyP1 SheafCohomology CategoryTheory CategoryTheory.Limits

namespace SheafCohDerived

section CechDeltaFunctorData

variable (k : Type) [Field k]

/-- Numerical data for the Čech `δ`-functor on `ℙ¹`: the dimensions
`h⁰(O(n))`, `h¹(O(n))`, their characteristic formulas, and the Euler identity. -/
structure CechDeltaFunctorP1 (k : Type) [Field k] where
  dimH0 : ℤ → ℕ
  dimH1 : ℤ → ℕ
  dimH0_nonneg : ∀ n : ℤ, 0 ≤ n → dimH0 n = (n + 1).toNat
  dimH0_neg : ∀ n : ℤ, n < 0 → dimH0 n = 0
  dimH1_nonneg : ∀ n : ℤ, 0 ≤ n → dimH1 n = 0
  dimH1_neg : ∀ n : ℤ, n < 0 → dimH1 n = (-n - 1).toNat
  euler : ∀ n : ℤ, (dimH0 n : ℤ) - (dimH1 n : ℤ) = n + 1

end CechDeltaFunctorData
end SheafCohDerived
end
