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
public import Instance.v1.Atlas.NumberTheoryI.code.ArithmeticFunctions
public section

open scoped Nat
open Finset Real Filter Asymptotics


namespace ArithFuncZ

structure IsMultiplicative (f : ArithFuncZ) : Prop where
  map_one : f 1 = 1
  map_mul_of_coprime : ∀ m n : ℤ, Int.gcd m n = 1 → f (m * n) = f m * f n

structure IsTotallyMultiplicative (f : ArithFuncZ) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ m n : ℤ, f (m * n) = f m * f n

end ArithFuncZ
