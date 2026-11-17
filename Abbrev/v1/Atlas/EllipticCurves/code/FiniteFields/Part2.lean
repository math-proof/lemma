/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Theorem.v1.Atlas.EllipticCurves.code.FiniteFields

@[expose] public section


open Polynomial in
/-- Notation `𝔽q p n` for the finite field with `p^n` elements, defined
as `GaloisField p n` (the splitting field of `X^(p^n) - X` over `𝔽_p`).
Matches Definition 3.4. -/
abbrev 𝔽q (p : ℕ) [Fact p.Prime] (n : ℕ) := GaloisField p n

