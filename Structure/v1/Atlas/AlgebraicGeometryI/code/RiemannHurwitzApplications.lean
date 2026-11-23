/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzApplications.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzDegree
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitzDegree
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.NormalExtension
public import Def.v1.Atlas.AlgebraicGeometryI.code.NormalExtension
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Height


public noncomputable section

open RiemannHurwitzFormula CanonicalSheafCurves RiemannHurwitzDegree

namespace RiemannHurwitzApplications

section GenusBounds

/-- Prop 39 (Lec, normal domain criterion): the data needed to express
integrality of a fraction in terms of local conditions at height-one primes. -/
structure NormalDomainLocalizationData (R : Type*) [CommRing R] [IsDomain R] where
  isIntegrallyClosed : IsIntegrallyClosed R
  intersection_property :
    ∀ (a b : R), b ≠ 0 →
    (∀ (p : Ideal R), p.IsPrime → p ≠ ⊥ → p.height ≤ (1 : ℕ∞) →
      ∃ (r s : R), s ∉ p ∧ a * s = b * r) →
    ∃ (q : R), a = b * q

end GenusBounds
end RiemannHurwitzApplications
end
