/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertFormulaOdd.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertSymbol
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HenselsLemma
import Abbrev.v1.Atlas.ArithmeticGeometry.code.HenselsLemma
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
open HilbertSymbol


noncomputable section

/-- The prime $p$ viewed as a unit in $\mathbb{Q}_p^\times$. -/
noncomputable def qpPrime (p : ℕ) [Fact (Nat.Prime p)] : ℚ_[p]ˣ :=
  Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out))

/-- The Legendre symbol $\left(\frac{v}{p}\right)$ of a $p$-adic unit $v \in \mathbb{Z}_p^\times$,
computed via the reduction mod $p$. -/
def padicUnitLegendre (v : ℤ_[p]ˣ) : ℤ :=
  legendreSym p (ZMod.val (PadicInt.toZMod (v : ℤ_[p])) : ℤ)

/-- A "primitive-unit" representative $p^\alpha \cdot u \in \mathbb{Q}_p^\times$
with exponent $\alpha \in \{0, 1\}$ and $u$ a $p$-adic integer unit. -/
noncomputable def padicPowerUnit (p : ℕ) [Fact (Nat.Prime p)]
    (α : Fin 2) (u : ℤ_[p]ˣ) : ℚ_[p]ˣ :=
  (qpPrime p) ^ (α : ℕ) * unitZpToQp u

/-- A "primitive-unit" representative $p^\alpha \cdot u \in \mathbb{Q}_p^\times$
with integer exponent $\alpha \in \mathbb{Z}$ (allowing both positive and negative powers of $p$). -/
noncomputable def padicPowerUnitZ (p : ℕ) [Fact (Nat.Prime p)]
    (α : ℤ) (u : ℤ_[p]ˣ) : ℚ_[p]ˣ :=
  (qpPrime p) ^ α * unitZpToQp u

end
