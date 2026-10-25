/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PicardProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Structure.v1.Atlas.AlgebraicGeometryI.code.PicardProjective


noncomputable section

namespace PicardProjective

open MvPolynomial


/-- The degree of a homogeneous fraction: numerator degree minus denominator degree. -/
def HomogFraction.degree (σ : Type*) (k : Type*) [Field k]
    (p : HomogFraction σ k) : ℤ :=
  (p.ndeg : ℤ) - (p.ddeg : ℤ)

/-- Equivalence relation on homogeneous fractions identifying those that represent
the same line bundle class in Pic(P^n). -/
def HomogFraction.PicEquiv (σ : Type*) (k : Type*) [Field k]
    (p q : HomogFraction σ k) : Prop :=
  ∃ (a b : MvPolynomial σ k) (da db : ℕ),
    a ≠ 0 ∧ b ≠ 0 ∧ a.IsHomogeneous da ∧ b.IsHomogeneous db ∧
    da = db ∧ Associated (p.num * b * q.den) (q.num * a * p.den)

end PicardProjective
end
