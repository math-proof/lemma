/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/NormalExtension.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem


namespace AlgebraicHartogs

/-- A height-one prime ideal in a commutative ring, bundled with the proofs that it is
prime and has height exactly one. -/
structure HeightOnePrime (A : Type*) [CommRing A] where
  asIdeal : Ideal A
  isPrime : asIdeal.IsPrime
  height_eq : asIdeal.height = 1

end AlgebraicHartogs
