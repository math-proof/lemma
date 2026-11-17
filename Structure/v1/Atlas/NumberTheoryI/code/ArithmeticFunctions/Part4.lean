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
public import Def.v1.Atlas.NumberTheoryI.code.ArithmeticFunctions.Part3
public section

open scoped Nat
open Finset Real Filter Asymptotics


structure ArithFunc.IsDirichletCharacter (χ : ArithFunc) : Prop where
  totallyMultiplicative : χ.IsTotallyMultiplicative
  periodic : ∃ m, 0 < m ∧ χ.IsPeriodic m


