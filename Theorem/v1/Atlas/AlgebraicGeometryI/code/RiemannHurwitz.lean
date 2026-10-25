/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Algebraic.Integral
import Theorem.v1.Atlas.AlgebraicGeometryI.code.NakayamaApplications
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.NakayamaApplications
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.FiniteMorphismDimension
import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRochGeneral
import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitz.Part2


noncomputable section

open Ideal Module

section RamificationDivisor

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]

example : (2 : ℤ) * 1 - 2 = 2 * (2 * 0 - 2) + 4 * (2 - 1) := by norm_num

example : (2 : ℤ) * 2 - 2 = 2 * (2 * 0 - 2) + 6 * (2 - 1) := by norm_num

example : (2 : ℤ) * 1 - 2 = 3 * (2 * 0 - 2) + 6 := by norm_num

example : (2 : ℤ) * 3 - 2 = 2 * (2 * 2 - 2) + 0 := by norm_num

end RamificationDivisor
end
