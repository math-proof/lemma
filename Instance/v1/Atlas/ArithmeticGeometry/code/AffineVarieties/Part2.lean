/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Nullstellensatz
import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part4
variable (k : Type*) [Field k]


section Corollary1217

open MvPolynomial

variable {n : ℕ}

/-- The affine coordinate ring $k[Z]$ inherits a commutative ring structure from the quotient. -/
noncomputable instance instCommRingAffineCoordinateRing {n : ℕ}
    (Z : Set (Fin n → AlgebraicClosure k)) :
    CommRing (AffineCoordinateRing Z) :=
  Ideal.Quotient.commRing (idealOverK Z)

/-- The affine coordinate ring $\overline{k}[Z]$ inherits a commutative ring structure
from the quotient. -/
noncomputable instance instCommRingAffineCoordinateRingBar {n : ℕ}
    (Z : Set (Fin n → AlgebraicClosure k)) :
    CommRing (AffineCoordinateRingBar Z) :=
  Ideal.Quotient.commRing (idealOfAlgebraicSet Z)

end Corollary1217
