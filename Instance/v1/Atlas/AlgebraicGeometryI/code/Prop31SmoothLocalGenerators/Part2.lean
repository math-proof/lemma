/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop31SmoothLocalGenerators.lean -/

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
import Def.v1.Atlas.AlgebraicGeometryI.code.Prop31SmoothLocalGenerators.Part2


noncomputable section

/-- The image maximal ideal in the quotient is maximal. -/
instance maxIdealInQuotient_P31_isMaximal {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint_P31 x) :
    (maxIdealInQuotient_P31 I x hI).IsMaximal := by
  apply Ideal.IsMaximal.map_of_surjective_of_ker_le
  · exact Ideal.Quotient.mk_surjective
  · rwa [Ideal.mk_ker]

/-- The image maximal ideal in the quotient is prime. -/
instance maxIdealInQuotient_P31_isPrime {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint_P31 x) :
    (maxIdealInQuotient_P31 I x hI).IsPrime :=
  (maxIdealInQuotient_P31_isMaximal I x hI).isPrime

end
