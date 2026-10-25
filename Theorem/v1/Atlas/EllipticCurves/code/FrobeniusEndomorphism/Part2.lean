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
import Def.v1.Atlas.EllipticCurves.code.FrobeniusEndomorphism
open Polynomial

universe u


namespace FrobeniusEndomorphism

variable {F : Type u} [Field F]

variable {W : WeierstrassCurve.Affine F} {φ : F →+* F}

variable [DecidableEq F]

omit [DecidableEq F] [CharP F p] [DecidableEq L] in
/-- The $n$-th iterate of Frobenius on an $F$-algebra $L$ fixes the image of any element
of $F = \mathbb{F}_{p^n}$, because by Fermat's little theorem $a^{p^n} = a$ for $a \in F$. -/
lemma iterateFrobenius_algebraMap (hcard : Fintype.card F = p ^ n) (a : F) :
    iterateFrobenius L p n (algebraMap F L a) = algebraMap F L a := by
  change (algebraMap F L a) ^ (p ^ n) = algebraMap F L a
  rw [← map_pow]
  congr 1
  rw [← hcard]
  exact FiniteField.pow_card a

end FrobeniusEndomorphism
