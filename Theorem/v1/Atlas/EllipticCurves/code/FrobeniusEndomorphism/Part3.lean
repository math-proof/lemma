/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FrobeniusEndomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Frobenius
import Abbrev.v1.Atlas.EllipticCurves.code.FrobeniusEndomorphism
open Polynomial

universe u


namespace FrobeniusEndomorphism

variable {F : Type u} [Field F]

variable {W : WeierstrassCurve.Affine F} {φ : F →+* F}

variable [DecidableEq F]

omit [DecidableEq F] [CharP F p] [DecidableEq L] in
/-- The $n$-th Frobenius iterate $x \mapsto x^{p^n}$ on $L$ fixes the coefficients of the
base change to $L$ of any curve defined over $\mathbb{F}_{p^n}$, since those coefficients
lie in the prime-field-fixed subfield. -/
lemma fixesCoeffs_iterateFrobenius (hcard : Fintype.card F = p ^ n)
    (W : WeierstrassCurve.Affine F) :
    FixesCoeffs (baseChange W (L := L)) (iterateFrobenius L p n) where
  fix_a₁ := iterateFrobenius_algebraMap hcard W.a₁
  fix_a₂ := iterateFrobenius_algebraMap hcard W.a₂
  fix_a₃ := iterateFrobenius_algebraMap hcard W.a₃
  fix_a₄ := iterateFrobenius_algebraMap hcard W.a₄
  fix_a₆ := iterateFrobenius_algebraMap hcard W.a₆

end FrobeniusEndomorphism
