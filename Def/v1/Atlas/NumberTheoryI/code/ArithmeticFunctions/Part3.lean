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
import Structure.v1.Atlas.NumberTheoryI.code.ArithmeticFunctions.Part3
open scoped Nat
open Finset Real Filter Asymptotics


def ArithFunc.IsPeriodic (f : ArithFunc) (m : ℕ) : Prop :=
  ∀ n : ℕ, f (n + m) = f n

noncomputable def ArithFunc.period (f : ArithFunc) : ℕ := by
  classical
  exact if h : ∃ m, 0 < m ∧ f.IsPeriodic m then Nat.find h else 0


