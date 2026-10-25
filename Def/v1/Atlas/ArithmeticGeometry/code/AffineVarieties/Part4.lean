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
import Theorem.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part2
variable (k : Type*) [Field k]


section Corollary1217

open MvPolynomial

variable {n : ℕ}

/-- The ideal $I_k(Z) \subseteq k[x_1, \ldots, x_n]$ of polynomials over $k$ vanishing on
$Z$, obtained by pulling back $I(Z)$ along the scalar extension map. -/
noncomputable def idealOverK {n : ℕ} (Z : Set (Fin n → AlgebraicClosure k)) :
    Ideal (MvPolynomial (Fin n) k) :=
  Ideal.comap (MvPolynomial.map (algebraMap k (AlgebraicClosure k)))
    (idealOfAlgebraicSet Z)

/-- A subset $Z \subseteq \overline{k}^n$ is *defined over* $k$ if its vanishing ideal
$I(Z)$ is the extension to $\overline{k}$ of $I_k(Z)$. -/
def IsDefinedOver {n : ℕ} (Z : Set (Fin n → AlgebraicClosure k)) : Prop :=
  idealOfAlgebraicSet Z =
    Ideal.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k)))
      (idealOverK Z)

/-- The affine coordinate ring $k[Z] = k[x_1, \ldots, x_n] / I_k(Z)$ over the base field. -/
noncomputable def AffineCoordinateRing {n : ℕ}
    (Z : Set (Fin n → AlgebraicClosure k)) :=
  MvPolynomial (Fin n) k ⧸ idealOverK Z

/-- The affine coordinate ring $\overline{k}[Z] = \overline{k}[x_1, \ldots, x_n] / I(Z)$ over
the algebraic closure. -/
def AffineCoordinateRingBar {n : ℕ}
    (Z : Set (Fin n → AlgebraicClosure k)) :=
  MvPolynomial (Fin n) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet Z

end Corollary1217
