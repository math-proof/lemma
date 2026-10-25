/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Hilbert2AdicCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertSymbol
import Instance.v1.Atlas.ArithmeticGeometry.code.Hilbert2AdicCore
open PadicInt HilbertSymbol


/-- The invariant $\epsilon(u) = (u - 1)/2 \bmod 2$ for a unit `u` in `ZMod 8`. -/
def epsilon_ZMod8 (u : (ZMod (2 ^ 3))ˣ) : ZMod 2 :=
  ((((u : ZMod (2 ^ 3)).val - 1) / 2 : ℕ) : ZMod 2)

/-- The invariant $\omega(u) = (u^2 - 1)/8 \bmod 2$ for a unit `u` in `ZMod 8`. -/
def omega_ZMod8 (u : (ZMod (2 ^ 3))ˣ) : ZMod 2 :=
  ((((u : ZMod (2 ^ 3)).val ^ 2 - 1) / 8 : ℕ) : ZMod 2)

/-- The closed-form expression $(-1)^{\epsilon(u)\epsilon(v) + \alpha\omega(v) + \beta\omega(u)}$
for the $2$-adic Hilbert symbol on units (Theorem 10.9). -/
def hilbert2Adic_formula
    (u₀ v₀ : (ZMod (2 ^ 3))ˣ) (α β : ℕ) : ℤ :=
  (-1 : ℤ) ^ ((epsilon_ZMod8 u₀ * epsilon_ZMod8 v₀ +
    α * omega_ZMod8 v₀ + β * omega_ZMod8 u₀).val)

