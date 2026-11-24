module
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.FieldTheory.Separable
public import Theorem.v1.Atlas.NumberTheoryI.code.LocalExtensions.Part2
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.LocalExtensions
open Polynomial Ideal IsLocalRing


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/EisensteinRamified.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]


namespace Polynomial

abbrev IsEisenstein (f : A[X]) : Prop :=
  f.IsEisensteinAt (IsLocalRing.maximalIdeal A)

end Polynomial
