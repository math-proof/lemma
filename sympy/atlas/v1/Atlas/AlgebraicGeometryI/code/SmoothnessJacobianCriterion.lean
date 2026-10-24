/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothnessJacobianCriterion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Maps

noncomputable section

/-- The maximal ideal of `k[x₁,…,xₙ]` corresponding to a `k`-rational point `x`:
the kernel of evaluation at `x`. -/
def maxIdealOfPoint_SJC {k : Type*} [Field k] {n : ℕ}
    (x : Fin n → k) : Ideal (MvPolynomial (Fin n) k) :=
  RingHom.ker (MvPolynomial.eval x)

/-- `maxIdealOfPoint_SJC x` is maximal: evaluation at a rational point gives a
ring homomorphism onto the field `k`. -/
instance maxIdealOfPoint_SJC_isMaximal {k : Type*} [Field k] {n : ℕ}
    (x : Fin n → k) : (maxIdealOfPoint_SJC x).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (fun c => ⟨MvPolynomial.C c, MvPolynomial.eval_C c⟩)

/-- Image of the point-maximal-ideal in the quotient `k[x]/I`: the maximal ideal
of the closed point `x` in the affine variety `V(I)`. -/
def maxIdealInQuotient_SJC {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (_ : I ≤ maxIdealOfPoint_SJC x) :
    Ideal (MvPolynomial (Fin n) k ⧸ I) :=
  Ideal.map (Ideal.Quotient.mk I) (maxIdealOfPoint_SJC x)

/-- The image of the point ideal in the quotient is maximal. -/
instance maxIdealInQuotient_SJC_isMaximal {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint_SJC x) :
    (maxIdealInQuotient_SJC I x hI).IsMaximal := by
  apply Ideal.IsMaximal.map_of_surjective_of_ker_le
  · exact Ideal.Quotient.mk_surjective
  · rwa [Ideal.mk_ker]

/-- The image of the point ideal in the quotient is prime (follows from maximal). -/
instance maxIdealInQuotient_SJC_isPrime {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint_SJC x) :
    (maxIdealInQuotient_SJC I x hI).IsPrime :=
  (maxIdealInQuotient_SJC_isMaximal I x hI).isPrime

/-- The **local ring at a `k`-rational point** `x` of an affine variety `V(I)`:
the localization of `k[x]/I` at the maximal ideal of `x`. -/
abbrev localRingAtPoint_SJC {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint_SJC x) :=
  Localization.AtPrime (maxIdealInQuotient_SJC I x hI)

/-- **Jacobian matrix** of a finite system `f₁,…,fₘ` of polynomials in
`x₁,…,xₙ` evaluated at the point `x`. -/
def jacobianMatrix_SJC {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k) (x : Fin n → k) :
    Matrix (Fin m) (Fin n) k :=
  fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (f i))
