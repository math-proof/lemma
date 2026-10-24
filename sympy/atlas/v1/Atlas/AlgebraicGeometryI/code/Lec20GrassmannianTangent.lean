/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianTangent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Grassmannian
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Trace

set_option maxHeartbeats 400000

open KaehlerDifferential Module

noncomputable section

universe u v w

section Proposition35

variable (R : Type u) [CommRing R]
variable (A : Type v) [CommRing A] [Algebra R A]

/-- Shorthand for the polynomial ring `k[x_0, …, x_n]` used in the Euler sequence section. -/
abbrev PolyRingLec20 := MvPolynomial (Fin (n + 1)) k

/-- The standard basis `(dx_0, …, dx_n)` of `Ω_{k[x_0,…,x_n]/k}` as a free module of
rank `n + 1`. -/
def euler_seq_kahler_basis :
    Basis (Fin (n + 1)) (PolyRingLec20 k n) (Ω[PolyRingLec20 k n⁄k]) :=
  KaehlerDifferential.mvPolynomialBasis k (Fin (n + 1))

/-- The module of Kähler differentials of `k[x_0,…,x_n]` is free. -/
instance euler_seq_kahler_free :
    Module.Free (PolyRingLec20 k n) (Ω[PolyRingLec20 k n⁄k]) :=
  inferInstance

/-- The module of Kähler differentials of `k[x_0,…,x_n]` is finitely generated. -/
instance euler_seq_kahler_finite :
    Module.Finite (PolyRingLec20 k n) (Ω[PolyRingLec20 k n⁄k]) :=
  Module.Finite.of_basis (euler_seq_kahler_basis k n)

/-- The tautological subspace `V ⊂ W` associated to a point `V ∈ Gr(k, W)`. -/
def tautologicalSubspace (kk : ℕ) (V : Module.Grassmannian F W kk) :
    Submodule F W :=
  V.toSubmodule

/-- The tautological quotient bundle fibre `W/V` at a point `V ∈ Gr(k, W)`. -/
abbrev tautologicalQuotient (kk : ℕ) (V : Module.Grassmannian F W kk) :=
  W ⧸ V.toSubmodule

/-- The tautological quotient `W/V` is a finite `F`-module. -/
instance tautologicalQuotient_finite (kk : ℕ) (V : Module.Grassmannian F W kk) :
    Module.Finite F (tautologicalQuotient F W kk V) :=
  V.finite_quotient

/-- The tautological quotient `W/V` is a projective `F`-module. -/
instance tautologicalQuotient_projective (kk : ℕ) (V : Module.Grassmannian F W kk) :
    Module.Projective F (tautologicalQuotient F W kk V) :=
  V.projective_quotient

/-- Tangent space of the Grassmannian at a point `V`, identified with `Hom(V, W/V)`. -/
abbrev grassmannianTangentSpace (kk : ℕ) (V : Module.Grassmannian F W kk) :=
  V.toSubmodule →ₗ[F] (W ⧸ V.toSubmodule)

/-- Cotangent space of the Grassmannian at a point `V`, identified with `Hom(W/V, V)`. -/
abbrev grassmannianCotangentSpace (kk : ℕ) (V : Module.Grassmannian F W kk) :=
  (W ⧸ V.toSubmodule) →ₗ[F] V.toSubmodule
