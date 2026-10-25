/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LinearEquivDivisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Def.v1.Atlas.AlgebraicGeometryI.code.LinearEquivDivisors.Part2


noncomputable section

open scoped nonZeroDivisors

namespace LinearEquivDivisors

variable {Y : Type*}

/-- Linear equivalence of Weil divisors is an equivalence relation. -/
theorem weilLinearlyEquivalent_equivalence (P : PrincipalDivisors Y) :
    Equivalence (WeilLinearlyEquivalent P) where
  refl D := by
    show D - D ∈ P
    simp [P.zero_mem]
  symm {a b} h := by
    show b - a ∈ P
    have : b - a = -(a - b) := by abel
    rw [this]
    exact P.neg_mem h
  trans {a b c} h1 h2 := by
    show a - c ∈ P
    have : a - c = (a - b) + (b - c) := by abel
    rw [this]
    exact P.add_mem h1 h2

/-- Linear equivalence of Weil divisors is reflexive. -/
theorem WeilLinearlyEquivalent.refl (P : PrincipalDivisors Y)
    (D : WeilDivisorGroup Y) :
    WeilLinearlyEquivalent P D D :=
  (weilLinearlyEquivalent_equivalence P).refl D

/-- Linear equivalence of Weil divisors is symmetric. -/
theorem WeilLinearlyEquivalent.symm (P : PrincipalDivisors Y)
    {D₁ D₂ : WeilDivisorGroup Y} (h : WeilLinearlyEquivalent P D₁ D₂) :
    WeilLinearlyEquivalent P D₂ D₁ :=
  (weilLinearlyEquivalent_equivalence P).symm h

/-- Linear equivalence of Weil divisors is transitive. -/
theorem WeilLinearlyEquivalent.trans (P : PrincipalDivisors Y)
    {D₁ D₂ D₃ : WeilDivisorGroup Y}
    (h₁ : WeilLinearlyEquivalent P D₁ D₂) (h₂ : WeilLinearlyEquivalent P D₂ D₃) :
    WeilLinearlyEquivalent P D₁ D₃ :=
  (weilLinearlyEquivalent_equivalence P).trans h₁ h₂

end LinearEquivDivisors
end
