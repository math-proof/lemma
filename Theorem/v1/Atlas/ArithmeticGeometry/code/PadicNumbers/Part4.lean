module
public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib
public import Def.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace PadicInt

open Finset PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

/-- The reduction $\mathbb{Z}_p \twoheadrightarrow \mathbb{Z}/p^m\mathbb{Z}$ is surjective. -/
theorem PadicInt.toZModPow_surjective (m : ℕ) :
    Function.Surjective (toZModPow m : ℤ_[p] →+* ZMod (p ^ m)) := by
  intro x
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  exact ⟨n, by simp [toZModPow, toZModHom]⟩

end PadicInt
