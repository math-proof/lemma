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
public import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties

@[expose] public section

variable (k : Type*) [Field k]


section GaloisCharacterization

variable [PerfectField k]

/-- The natural action of the absolute Galois group $\mathrm{Gal}(\overline{k}/k)$ on affine
$n$-space by coordinate-wise application. -/
noncomputable instance galoisActionAffineSpace (n : ℕ) :
    MulAction (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (AffineSpace_k k n) where
  smul σ P := fun i => σ (P i)
  one_smul P := by ext i; simp
  mul_smul σ τ P := by ext i; simp [AlgEquiv.mul_apply]

end GaloisCharacterization
