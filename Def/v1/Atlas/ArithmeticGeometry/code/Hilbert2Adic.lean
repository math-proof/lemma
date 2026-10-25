/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2Adic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.LinearCombination
import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertSymbol
import Theorem.v1.Atlas.ArithmeticGeometry.code.Hilbert2Adic
open Polynomial PadicInt HilbertSymbol


noncomputable section

/-- Primitive mod-$8$ solvability of $z^2 = u x^2 + v y^2$ over $\mathbb{Z}_2$: there exist
$x_0, y_0, z_0 \in \mathbb{Z}/8\mathbb{Z}$, not all non-units, satisfying the equation. -/
def HasPrimitiveSolutionMod8_one (u v : ℤ_[2]ˣ) : Prop :=
  ∃ x₀ y₀ z₀ : ZMod (2 ^ 3),
    (IsUnit x₀ ∨ IsUnit y₀ ∨ IsUnit z₀) ∧
    z₀ ^ 2 = (PadicInt.toZModPow 3 (↑u)) * x₀ ^ 2 + (PadicInt.toZModPow 3 (↑v)) * y₀ ^ 2

/-- Primitive mod-$8$ solvability of $z^2 = 2u x^2 + v y^2$ over $\mathbb{Z}_2$. -/
def HasPrimitiveSolutionMod8_two (u v : ℤ_[2]ˣ) : Prop :=
  ∃ x₀ y₀ z₀ : ZMod (2 ^ 3),
    (IsUnit x₀ ∨ IsUnit y₀ ∨ IsUnit z₀) ∧
    z₀ ^ 2 = (2 : ZMod (2 ^ 3)) * (PadicInt.toZModPow 3 (↑u)) * x₀ ^ 2 +
              (PadicInt.toZModPow 3 (↑v)) * y₀ ^ 2

/-- Lift of a $\mathbb{Z}_2$-unit to a $\mathbb{Q}_2$-unit (i.e. multiplication by $1$). -/
noncomputable def padicUnit_one (u : ℤ_[2]ˣ) : ℚ_[2]ˣ :=
  ((Units.isUnit u).map (algebraMap ℤ_[2] ℚ_[2])).unit

/-- The $\mathbb{Q}_2$-unit $2u$ obtained by multiplying the lift of `u` by $2$. -/
noncomputable def padicUnit_two (u : ℤ_[2]ˣ) : ℚ_[2]ˣ :=
  ((isUnit_of_invertible (2 : ℚ_[2])).mul
    ((Units.isUnit u).map (algebraMap ℤ_[2] ℚ_[2]))).unit

end
