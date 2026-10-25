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
import Theorem.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part3
open scoped LinearAlgebra.Projectivization


noncomputable section

set_option synthInstance.maxHeartbeats 80000

open MvPolynomial Finsupp

open scoped LinearAlgebra.Projectivization

namespace Corollary1326

variable {n : ℕ} (k : Type*) [Field k]

/-- Ring isomorphism between coordinate rings induced by equality of varieties
$V = V'$. -/
def coordinateRingEquiv
    (V V' : Set (Fin n → k)) (hVV' : V = V') :
    (MvPolynomial (Fin n) k ⧸ vanishingIdeal k V) ≃+*
    (MvPolynomial (Fin n) k ⧸ vanishingIdeal k V') :=
  Ideal.quotEquivOfEq (vanishingIdeal_eq_of_set_eq k V V' hVV')

/-- Equal irreducible varieties give isomorphic function fields. -/
def functionFieldEquiv
    (V V' : Set (Fin n → k)) (hVV' : V = V')
    [(vanishingIdeal k V).IsPrime] [(vanishingIdeal k V').IsPrime] :
    FractionRing (MvPolynomial (Fin n) k ⧸ vanishingIdeal k V) ≃+*
    FractionRing (MvPolynomial (Fin n) k ⧸ vanishingIdeal k V') := by
  haveI : IsDomain (MvPolynomial (Fin n) k ⧸ vanishingIdeal k V) :=
    Ideal.Quotient.isDomain _
  haveI : IsDomain (MvPolynomial (Fin n) k ⧸ vanishingIdeal k V') :=
    Ideal.Quotient.isDomain _
  exact IsFractionRing.ringEquivOfRingEquiv (coordinateRingEquiv k V V' hVV')

/-- Coordinate-ring isomorphism between the affine part of the projective
closure of $V(I)$ and the affine variety $V(I)$ itself (Corollary 13.26). -/
def coordinateRingEquiv_of_projective_closure
    (I : Ideal (MvPolynomial (Fin n) k)) :
    (MvPolynomial (Fin n) k ⧸
      vanishingIdeal k {P : Fin n → k |
        ∀ g ∈ ProjectiveClosure.homogenizeIdeal I,
          eval ((0 : Fin (n + 1)).insertNth (1 : k) P) g = 0}) ≃+*
    (MvPolynomial (Fin n) k ⧸
      vanishingIdeal k {P : Fin n → k | ∀ f ∈ I, eval P f = 0}) :=
  coordinateRingEquiv k _ _
    (Theorem1323.projective_closure_cap_affine_eq k I)

end Corollary1326
end
