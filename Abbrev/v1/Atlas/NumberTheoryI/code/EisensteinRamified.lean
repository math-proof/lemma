/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/EisensteinRamified.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.FieldTheory.Separable
import Theorem.v1.Atlas.NumberTheoryI.code.LocalExtensions.Part2
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.LocalExtensions
open Polynomial Ideal IsLocalRing

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]


namespace Polynomial

abbrev IsEisenstein (f : A[X]) : Prop :=
  f.IsEisensteinAt (IsLocalRing.maximalIdeal A)

end Polynomial
