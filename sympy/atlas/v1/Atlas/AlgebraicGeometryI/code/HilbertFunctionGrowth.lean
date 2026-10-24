/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/HilbertFunctionGrowth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Nat.Choose.Bounds

set_option maxHeartbeats 400000

noncomputable section

open Nat MvPolynomial

/-- The Hilbert function `n ↦ C(n+d, d)` of the polynomial ring in `d` variables;
the prototypical reference for `Θ(n^d)` growth. -/
def polyDimFun (d : ℕ) (n : ℕ) : ℕ := (n + d).choose d

/-- Filtration on `A` induced by an algebra surjection `f`: the `n`-th piece is the
image of polynomials of total degree `≤ n` under `f`. -/
def generatorFiltration {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
    {m : ℕ} (f : MvPolynomial (Fin m) k →ₐ[k] A) (n : ℕ) : Submodule k A :=
  Submodule.map f.toLinearMap (MvPolynomial.restrictTotalDegree (Fin m) k n)

/-- The Hilbert function `D_V(n)` for the filtration `generatorFiltration f`: the
`k`-dimension of its `n`-th piece. -/
def dimFun {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A]
    {m : ℕ} (f : MvPolynomial (Fin m) k →ₐ[k] A) (n : ℕ) : ℕ :=
  Module.finrank k (generatorFiltration f n)

/-- Comparison via Noether normalization: the Hilbert function `dimFun f` is sandwiched
between `polyDimFun d` and a constant multiple of it, where `d` is the Krull dimension. -/
