/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HilbertSymbol.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Normed.Group.Ultra
import Theorem.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol
open scoped Classical

variable (F : Type*) [Field F]


namespace hilbertSymbol

variable {F : Type*} [Field F]

/-- The $p$-adic Hilbert symbol $(a, b)_p$, defined as the Hilbert symbol over the
$p$-adic numbers $\mathbb{Q}_p$. -/
noncomputable def padicHilbertSymbol (p : ℕ) [Fact (Nat.Prime p)] (a b : ℚ_[p]ˣ) : ℤ :=
  hilbertSymbol ℚ_[p] a b

namespace padicHilbertSymbol

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The real Hilbert symbol $(a, b)_\infty$, defined as the Hilbert symbol over $\mathbb{R}$. -/
noncomputable def realHilbertSymbol (a b : ℝˣ) : ℤ :=
  hilbertSymbol ℝ a b

namespace realHilbertSymbol

/-- Helper: when $\|a\| \le \|b\|$, the quotient $a/b$ lies in $\mathbb{Z}_p$
(has $p$-adic norm $\le 1$). -/
noncomputable def toZpDiv {a b : ℚ_[p]} (h : ‖a‖ ≤ ‖b‖) : ℤ_[p] :=
  ⟨a / b, by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)⟩

/-- Inclusion of $p$-adic integer units into $p$-adic field units: $\mathbb{Z}_p^\times
\hookrightarrow \mathbb{Q}_p^\times$. -/
noncomputable def unitZpToQp {p : ℕ} [Fact (Nat.Prime p)] (u : ℤ_[p]ˣ) : ℚ_[p]ˣ :=
  Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom u

end realHilbertSymbol
end padicHilbertSymbol
end hilbertSymbol
