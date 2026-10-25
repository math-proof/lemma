/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2AdicCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertSymbol
open PadicInt HilbertSymbol


/-- Reduction of a $2$-adic unit `u : ℤ_[2]ˣ` to a unit in `ZMod (2 ^ n)` via `toZModPow`. -/
noncomputable def toZModPow_unit (n : ℕ) (u : ℤ_[2]ˣ) : (ZMod (2 ^ n))ˣ :=
  (Units.isUnit u).map (toZModPow n : ℤ_[2] →+* ZMod (2 ^ n)) |>.unit

/-- Decidable predicate: there exist `x₀, y₀, z₀ ∈ ZMod 8` with at least one a unit such
that $z_0^2 = u_0 x_0^2 + v_0 y_0^2$ (primitive solution mod $8$ for the case $\alpha = 0$). -/
@[reducible]
def hasPrimSolMod8_one_dec (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Prop :=
  ∃ x₀ y₀ z₀ : ZMod (2 ^ 3),
    (IsUnit x₀ ∨ IsUnit y₀ ∨ IsUnit z₀) ∧
    z₀ ^ 2 = (↑u₀ : ZMod (2 ^ 3)) * x₀ ^ 2 + (↑v₀ : ZMod (2 ^ 3)) * y₀ ^ 2

/-- Decidable predicate: there exist `x₀, y₀, z₀ ∈ ZMod 8` with at least one a unit such
that $z_0^2 = 2 u_0 x_0^2 + v_0 y_0^2$ (primitive solution mod $8$ for the case $\alpha = 1$). -/
@[reducible]
def hasPrimSolMod8_two_dec (u₀ v₀ : (ZMod (2 ^ 3))ˣ) : Prop :=
  ∃ x₀ y₀ z₀ : ZMod (2 ^ 3),
    (IsUnit x₀ ∨ IsUnit y₀ ∨ IsUnit z₀) ∧
    z₀ ^ 2 = (2 : ZMod (2 ^ 3)) * (↑u₀ : ZMod (2 ^ 3)) * x₀ ^ 2 +
              (↑v₀ : ZMod (2 ^ 3)) * y₀ ^ 2

