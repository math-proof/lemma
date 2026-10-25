/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArithmeticFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Topology.Order.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Structure.v1.Atlas.NumberTheoryI.code.ArithmeticFunctions.Part4
open scoped Nat
open Finset Real Filter Asymptotics


noncomputable def ArithFunc.one : ArithFunc :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℂ)

noncomputable def ArithFunc.vonMangoldt : ArithFunc :=
  Complex.ofRealHom.toZeroHom.comp ArithmeticFunction.vonMangoldt

def DirichletCharacter.IsInducedBy {R : Type*} [CommMonoidWithZero R]
    {m₁ m₂ : ℕ} (χ₂ : DirichletCharacter R m₂) (χ₁ : DirichletCharacter R m₁)
    (h : m₁ ∣ m₂) : Prop :=
  χ₂ = DirichletCharacter.changeLevel h χ₁


def DirichletCharacter.IsPrincipal {R : Type*} [CommMonoidWithZero R]
    {m : ℕ} (χ : DirichletCharacter R m) : Prop :=
  χ = 1

noncomputable def principalDirichletChar (R : Type*) [CommMonoidWithZero R] (m : ℕ) :
    DirichletCharacter R m :=
  1

