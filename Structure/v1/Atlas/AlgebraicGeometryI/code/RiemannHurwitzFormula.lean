/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Discriminant
import Def.v1.Atlas.AlgebraicGeometryI.code.CoherentSheavesCurves.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CoherentSheavesCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitz
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalDivisorDecomposition
import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitz
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalDivisorDecomposition.Part4
import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzFormula


noncomputable section

open Ideal Module

namespace RiemannHurwitzFormula

section DVRRamification

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

variable {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

variable [Algebra R S]

/-- Numerical data attached to a finite morphism `f : X → Y` of smooth curves:
the degree, the degrees of the canonical divisors on source and target, and
the degree of the ramification divisor, with non-negativity/positivity hypotheses. -/
structure CurveMorphismData where
  degree : ℤ
  deg_KX : ℤ
  deg_KY : ℤ
  deg_R : ℤ
  h_deg_R_nonneg : 0 ≤ deg_R
  h_deg_pos : 0 < degree

end DVRRamification
end RiemannHurwitzFormula
end
