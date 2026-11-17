/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Ideal.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Localization.NormTrace
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec6FunctionFields

@[expose] public section

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
