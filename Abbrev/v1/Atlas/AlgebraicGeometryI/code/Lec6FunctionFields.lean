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
public import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec6FunctionFields
open CategoryTheory Opposite


@[expose] public noncomputable section

namespace Lec6

open AlgebraicGeometry TopologicalSpace

/-- The function field of a domain `R`, defined as its fraction field
(Lec 6, Def 14, affine viewpoint). -/
abbrev functionField (R : Type*) [CommRing R] [IsDomain R] : Type _ :=
  FractionRing R

end Lec6
end
