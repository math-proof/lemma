/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/OrdinarySupersingular.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.EllipticCurves.code.Isogenies
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Lemma.Complex.Atlas.v1.EllipticCurves.code.PointCounting
import Lemma.Complex.Atlas.v1.EllipticCurves.code.JInvariant
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EndomorphismAlgebra
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EndAlgClassification
import sympy.atlas.v1.Atlas.EllipticCurves.code.PointCounting
import sympy.atlas.v1.Atlas.EllipticCurves.code.JInvariant
import sympy.atlas.v1.Atlas.EllipticCurves.code.EndomorphismAlgebra
import sympy.atlas.v1.Atlas.EllipticCurves.code.EndAlgClassification

import Mathlib.Algebra.CharP.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

universe u

namespace OrdinarySupersingular

variable {F : Type u} [Field F] [DecidableEq F]

/-- The separable degree of an isogeny `φ : E₁ → E₂`, i.e., the degree of the separable part of
the induced extension of function fields. -/
def pTorsionSubgroup (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] : Set E.Point :=
  { P | (p : ℤ) • P = 0 }

/-- An elliptic curve `E` over a field of characteristic `p` is supersingular if its `p`-torsion
subgroup is trivial. -/
def IsSupersingular (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] : Prop :=
  ∀ P : E.Point, (p : ℤ) • P = 0 → P = 0

/-- An elliptic curve `E` over a field of characteristic `p` is ordinary if it admits a nonzero
`p`-torsion point. -/
def IsOrdinary (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] : Prop :=
  ∃ P : E.Point, (p : ℤ) • P = 0 ∧ P ≠ 0

/-- The Frobenius discriminant of `E/F_q`: `t² - 4q`, where `t = tr π_E`. -/
noncomputable def frobDiscriminant (E : WeierstrassCurve.Affine F) : ℤ :=
  (Hasse.traceFrobenius E) ^ 2 - 4 * (Fintype.card F : ℤ)

/-- The predicate that the Frobenius endomorphism is not an integer (i.e., `t² ≠ 4q`), so that
`ℤ[π_E]` is a non-trivial quadratic order. -/
def frobNotInt (E : WeierstrassCurve.Affine F) : Prop :=
  (Hasse.traceFrobenius E) ^ 2 ≠ 4 * (Fintype.card F : ℤ)

/-- The conductor of the order `ℤ[π_E]` inside the maximal quadratic order with discriminant
`frobDiscriminant E`. -/
end EC_Application

end OrdinarySupersingularClassification
