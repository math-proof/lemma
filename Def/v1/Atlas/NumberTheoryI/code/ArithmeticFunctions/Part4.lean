/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArithmeticFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.SmoothNumbers
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Topology.Order.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Nat.Totient
public import Structure.v1.Atlas.NumberTheoryI.code.ArithmeticFunctions.Part4

@[expose] public section

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

