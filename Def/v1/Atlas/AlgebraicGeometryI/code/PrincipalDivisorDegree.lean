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
set_option maxHeartbeats 1600000

open Polynomial


noncomputable section

/-- The degree of a principal divisor: difference of k-dimensions of A/I and A/J,
where I, J are two ideals representing a divisor of the form (p) - (q). -/
def principalDivisorDegree (k : Type*) [Field k] (A : Type*) [CommRing A]
    [IsDomain A] [Algebra k A] (I J : Ideal A) : ℤ :=
  (Module.finrank k (A ⧸ I) : ℤ) - (Module.finrank k (A ⧸ J) : ℤ)

/-- Witness for principal-divisor data on S: there exists s ∈ S\{0} with q·s = p in S,
i.e. p/q is a regular function in some sense. -/
def IsPrincipalDivisorData (k : Type*) [Field k] (S : Type*) [CommRing S] [IsDomain S]
    [Algebra (Polynomial k) S] (p q : Polynomial k) : Prop :=
  ∃ (s : S), s ≠ 0 ∧ algebraMap (Polynomial k) S q * s = algebraMap (Polynomial k) S p

end
