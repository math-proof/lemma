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
import Theorem.v1.Atlas.EllipticCurves.code.FrobeniusEndomorphism.Part3
open Polynomial

universe u


namespace FrobeniusEndomorphism

variable {F : Type u} [Field F]

variable {W : WeierstrassCurve.Affine F} {φ : F →+* F}

variable [DecidableEq F]

/-- The Frobenius endomorphism on points of $W_L$ for $W/\mathbb{F}_{p^n}$
(Definition 4.24): the self-map of points sending $(x, y) \mapsto (x^{p^n}, y^{p^n})$.
This is the geometric Frobenius whose fixed points are the $\mathbb{F}_{p^n}$-rational points. -/
noncomputable def frobeniusPointMap (hcard : Fintype.card F = p ^ n)
    (W : WeierstrassCurve.Affine F) :
    (baseChange W (L := L)).Point → (baseChange W (L := L)).Point :=
  pointMap (fixesCoeffs_iterateFrobenius hcard W) (iterateFrobenius L p n).injective

end FrobeniusEndomorphism
