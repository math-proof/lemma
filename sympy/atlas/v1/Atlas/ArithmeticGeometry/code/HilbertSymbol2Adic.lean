/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol2Adic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Hilbert2Adic
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Hilbert2Adic
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Hilbert2AdicCore
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertPrimitiveSolutions
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Hilbert2AdicCore
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions

open PadicInt HilbertSymbol

noncomputable section

/-- The function $\varepsilon(u) = (u - 1) / 2 \pmod{2}$ applied to a $2$-adic unit $u$, computed
via its image in $(\mathbb{Z}/8\mathbb{Z})^\times$. -/
def epsilon_padic (u : ℤ_[2]ˣ) : ZMod 2 :=
  epsilon_ZMod8 (toZModPow_unit 3 u)

/-- The function $\omega(u) = (u^2 - 1) / 8 \pmod{2}$ applied to a $2$-adic unit $u$, computed
via its image in $(\mathbb{Z}/8\mathbb{Z})^\times$. -/
def omega_padic (u : ℤ_[2]ˣ) : ZMod 2 :=
  omega_ZMod8 (toZModPow_unit 3 u)

/-- The element $2 \in \mathbb{Q}_2^\times$, viewed as a unit. -/
noncomputable def twoQp : ℚ_[2]ˣ := (isUnit_of_invertible (2 : ℚ_[2])).unit
