/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop1228.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Ideal.Norm.RelNorm
open Module Ideal

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra


noncomputable def discrIdeal (A : Type*) (B : Type*)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B] : Ideal A :=
  Ideal.spanNorm A (differentIdeal A B)

