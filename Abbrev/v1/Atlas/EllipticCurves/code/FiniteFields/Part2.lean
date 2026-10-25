/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Data.Nat.Prime.Basic
import Theorem.v1.Atlas.EllipticCurves.code.FiniteFields


open Polynomial in
/-- Notation `𝔽q p n` for the finite field with `p^n` elements, defined
as `GaloisField p n` (the splitting field of `X^(p^n) - X` over `𝔽_p`).
Matches Definition 3.4. -/
abbrev 𝔽q (p : ℕ) [Fact p.Prime] (n : ℕ) := GaloisField p n

