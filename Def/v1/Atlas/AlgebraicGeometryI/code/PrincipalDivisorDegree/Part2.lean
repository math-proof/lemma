/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PrincipalDivisorDegree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutTheorem
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.BezoutTheorem
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochGeneral
public import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRochGeneral
public import Class.v1.Atlas.AlgebraicGeometryI.code.PrincipalDivisorDegree

@[expose] public section

set_option maxHeartbeats 1600000

open Polynomial


noncomputable section

namespace PrincipalDivisorDegZero

open Module

/-- Degree of a principal divisor in S: dim_k(S/I) - dim_k(S/J). -/
def principalDivisorDeg (k : Type*) [Field k] (S : Type*) [CommRing S]
    [IsDomain S] [Algebra k S] (I J : Ideal S) : ℤ :=
  (finrank k (S ⧸ I) : ℤ) - (finrank k (S ⧸ J) : ℤ)

end PrincipalDivisorDegZero
end
