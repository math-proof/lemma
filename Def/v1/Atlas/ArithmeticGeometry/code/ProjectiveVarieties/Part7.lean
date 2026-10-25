/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Theorem.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part4
open scoped LinearAlgebra.Projectivization


noncomputable section

set_option synthInstance.maxHeartbeats 80000

open MvPolynomial Finsupp

open scoped LinearAlgebra.Projectivization

namespace Corollary1326

variable {n : ℕ} (k : Type*) [Field k]

/-- Coordinate-ring isomorphism induced by `affinePart_eq_dehomogenizedIdeal_zeroLocus`. -/
def coordinateRingEquiv_of_affinePart
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) :
    (MvPolynomial (Fin n) k ⧸
      vanishingIdeal k {P : Fin n → k |
        ∀ f ∈ I, eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f = 0}) ≃+*
    (MvPolynomial (Fin n) k ⧸
      vanishingIdeal k {P : Fin n → k |
        ∀ g ∈ I.map (AffineParts.dehomogenize k 0), eval P g = 0}) :=
  coordinateRingEquiv k _ _
    (affinePart_eq_dehomogenizedIdeal_zeroLocus k I)

/-- Function-field isomorphism for the two presentations of an irreducible
affine piece. -/
def functionFieldEquiv_of_affinePart
    (I : Ideal (MvPolynomial (Fin (n + 1)) k))
    [(vanishingIdeal k {P : Fin n → k |
        ∀ f ∈ I, eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f = 0}).IsPrime]
    [(vanishingIdeal k {P : Fin n → k |
        ∀ g ∈ I.map (AffineParts.dehomogenize k 0), eval P g = 0}).IsPrime] :
    FractionRing (MvPolynomial (Fin n) k ⧸
      vanishingIdeal k {P : Fin n → k |
        ∀ f ∈ I, eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f = 0}) ≃+*
    FractionRing (MvPolynomial (Fin n) k ⧸
      vanishingIdeal k {P : Fin n → k |
        ∀ g ∈ I.map (AffineParts.dehomogenize k 0), eval P g = 0}) :=
  functionFieldEquiv k _ _
    (affinePart_eq_dehomogenizedIdeal_zeroLocus k I)

end Corollary1326
end
