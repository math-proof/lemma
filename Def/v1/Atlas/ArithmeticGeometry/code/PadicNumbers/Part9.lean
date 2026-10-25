/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Order.DirectedInverseSystem
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib
import Theorem.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part4


namespace PadicInt

open Finset PadicInt

variable {p : ℕ} [hp : Fact p.Prime]

/-- Ring isomorphism $\mathbb{Z}_p / (p^m) \simeq \mathbb{Z}/p^m\mathbb{Z}$ obtained from the
first isomorphism theorem applied to `toZModPow m`. -/
noncomputable def PadicInt.quotientSpanPowPEquivZMod (m : ℕ) :
    ℤ_[p] ⧸ (Ideal.span {(p : ℤ_[p]) ^ m}) ≃+* ZMod (p ^ m) := by
  rw [← ker_toZModPow m]
  exact RingHom.quotientKerEquivOfSurjective (PadicInt.toZModPow_surjective m)

end Theorem48

open PadicInt in
/-- Corollary 4.9: the ring isomorphism $\mathbb{Z}_p / (p^m) \simeq \mathbb{Z}/p^m\mathbb{Z}$. -/
noncomputable def PadicInt.corollary_4_9 (p : ℕ) [Fact p.Prime] (m : ℕ) :
    ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ m} ≃+* ZMod (p ^ m) := by
  rw [← ker_toZModPow (p := p) m]
  exact RingHom.quotientKerEquivOfSurjective (PadicInt.toZModPow_surjective m)

section PadicValuation

noncomputable section

open PadicInt Classical

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The $p$-adic valuation on $\mathbb{Z}_p$ extended to $\mathbb{N} \cup \{\infty\}$:
$v(0) = \infty$ and $v(a) = \mathrm{PadicInt.valuation}(a)$ otherwise. -/
def padicValuationDef (a : ℤ_[p]) : WithTop ℕ :=
  if a = 0 then ⊤ else ↑(PadicInt.valuation a)

end
end PadicValuation
