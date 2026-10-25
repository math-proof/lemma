/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Away.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.SheafCohomology.Part2


namespace SheafCohomology

section SheafCondition

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- `H⁰(ℙ¹, O(n))`, realized concretely as the Čech `H⁰` of degree `n` sections. -/
abbrev H0 (n : ℤ) : Type := ↥(CechH0 k n)

/-- `H¹(ℙ¹, O(n))`, realized concretely as the quotient of Laurent series in one
variable by the sum of "non-negative degree" and "degree `≤ n`" subspaces. -/
abbrev H1 (n : ℤ) : Type := (ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)

end SheafCondition
end SheafCohomology
