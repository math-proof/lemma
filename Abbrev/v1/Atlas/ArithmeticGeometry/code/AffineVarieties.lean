/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Nullstellensatz
@[expose] public section

variable (k : Type*) [Field k]


/-- Affine $n$-space over $k$, defined as $\overline{k}^n$, i.e. tuples in the algebraic
closure. -/
abbrev AffineSpace_k (n : ℕ) : Type _ := Fin n → AlgebraicClosure k

