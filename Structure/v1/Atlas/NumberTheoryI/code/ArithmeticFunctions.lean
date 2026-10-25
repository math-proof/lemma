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
import Instance.v1.Atlas.NumberTheoryI.code.ArithmeticFunctions
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
