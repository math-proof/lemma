/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Localization.NormTrace
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec6FunctionFields
open CategoryTheory Opposite


noncomputable section

namespace Lec6

open AlgebraicGeometry TopologicalSpace

/-- The function field `K(X)` of an integral scheme `X` is a field
(Lec 6, Def 14 setting). -/
instance functionField_field (X : AlgebraicGeometry.Scheme) [IsIntegral X] :
    Field X.functionField := inferInstance

/-- For affine `Spec R` with `R` a domain, the function field is the
fraction field of `R` (Lec 6, Def 14 in the affine case). -/
instance functionField_isFractionRing_affine (R : CommRingCat) [IsDomain R] :
    IsFractionRing R (AlgebraicGeometry.Spec R).functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine R

end Lec6
end
