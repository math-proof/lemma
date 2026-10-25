/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PrincipalDivisorDegree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutTheorem
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.BezoutTheorem
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochGeneral
import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRochGeneral
import Def.v1.Atlas.AlgebraicGeometryI.code.PrincipalDivisorDegree
set_option maxHeartbeats 1600000

open Polynomial


noncomputable section

/-- Type class encoding the completeness condition for a curve algebra S over k[X]:
principal divisors of regular functions have equal numerator and denominator degrees. -/
class IsCompleteCurveAlg (k : Type*) [Field k] (S : Type*) [CommRing S] [IsDomain S]
    [Algebra (Polynomial k) S] where
  deg_eq_of_principal : ∀ (p q : Polynomial k), p ≠ 0 → q ≠ 0 →
    IsPrincipalDivisorData k S p q → p.natDegree = q.natDegree

end
