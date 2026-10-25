/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzSheafIso.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
open Ideal UniqueFactorizationMonoid

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra


namespace RiemannHurwitzSheaf

variable (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsDomain A] [IsDedekindDomain A] [IsDedekindDomain B]
  [Module.IsTorsionFree A B] [Module.Finite A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

end RiemannHurwitzSheaf
