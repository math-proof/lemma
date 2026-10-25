/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SeparatednessCriterion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic


noncomputable section

open Nat MvPolynomial

/-- The growth (Hilbert) function of the polynomial ring `k[x_0, …, x_{d-1}]`
in degree `n`: `(n + d choose d)`. -/
def growthFun_polyring (d : ℕ) (n : ℕ) : ℕ := (n + d).choose d

/-- Filtration of a finitely-generated algebra by total-degree truncation:
the image under a presentation `f` of polynomials of total degree `≤ n`. -/
def generatorFiltration' {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
    {m : ℕ} (f : MvPolynomial (Fin m) k →ₐ[k] A) (n : ℕ) : Submodule k A :=
  Submodule.map f.toLinearMap (MvPolynomial.restrictTotalDegree (Fin m) k n)

/-- Growth function of a finitely-generated algebra `A` along a presentation
`f`: the `k`-dimension of the degree-`n` filtration piece. -/
def growthFun {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
    {m : ℕ} (f : MvPolynomial (Fin m) k →ₐ[k] A) (n : ℕ) : ℕ :=
  Module.finrank k (generatorFiltration' f n)

end
