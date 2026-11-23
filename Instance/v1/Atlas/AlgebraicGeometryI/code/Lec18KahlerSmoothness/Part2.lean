/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec18KahlerSmoothness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec18KahlerSmoothness.Part2
@[expose] public section

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 400000


noncomputable section

open IsLocalRing

/-- The image of `m_x` in `k[x_1,…,x_n]/I` is maximal. -/
instance maxIdealOfPointInQuotient_isMaximal {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint x) :
    (maxIdealOfPointInQuotient I x hI).IsMaximal := by
  apply Ideal.IsMaximal.map_of_surjective_of_ker_le
  · exact Ideal.Quotient.mk_surjective
  · rwa [Ideal.mk_ker]

/-- The image of `m_x` in `k[x_1,…,x_n]/I` is prime (since maximal ideals are prime). -/
instance maxIdealOfPointInQuotient_isPrime {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint x) :
    (maxIdealOfPointInQuotient I x hI).IsPrime :=
  (maxIdealOfPointInQuotient_isMaximal I x hI).isPrime

end
