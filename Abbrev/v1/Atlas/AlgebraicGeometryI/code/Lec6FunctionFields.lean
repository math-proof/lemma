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
import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec6FunctionFields
open CategoryTheory Opposite


noncomputable section

namespace Lec6

open AlgebraicGeometry TopologicalSpace

/-- The function field of a domain `R`, defined as its fraction field
(Lec 6, Def 14, affine viewpoint). -/
abbrev functionField (R : Type*) [CommRing R] [IsDomain R] : Type _ :=
  FractionRing R

end Lec6
end
