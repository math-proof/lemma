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
open scoped Classical


namespace HilbertSymbol

section Defs

variable (F : Type*) [Field F]

/-- The equation $ax^2 + by^2 = 1$ has a solution $(x, y) \in F^2$. -/
def IsSolvable (a b : Fˣ) : Prop :=
  ∃ x y : F, (a : F) * x ^ 2 + (b : F) * y ^ 2 = 1

/-- The quadratic form $z^2 - ax^2 - by^2$ represents zero non-trivially over $F$,
i.e., $z^2 = ax^2 + by^2$ has a solution with $(x, y, z) \neq (0, 0, 0)$. -/
def RepresentsZero (a b : Fˣ) : Prop :=
  ∃ x y z : F, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ z ^ 2 = (a : F) * x ^ 2 + (b : F) * y ^ 2

/-- The unit $a \in F^\times$ is a norm from the quadratic extension $F(\sqrt{b})$,
i.e., there exist $z, y \in F$ with $z^2 - b y^2 = a$. -/
def IsNormFromSqrtExt (a b : Fˣ) : Prop :=
  ∃ z y : F, z ^ 2 - (b : F) * y ^ 2 = (a : F)

end Defs

section PadicDef

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The equation $ax^2 + by^2 = z^2$ admits a primitive $p$-adic integer solution,
i.e., one with $x, y, z \in \mathbb{Z}_p$ where at least one of them is a unit. -/
def HasPrimitiveSolution (a b : ℚ_[p]ˣ) : Prop :=
  ∃ x y z : ℤ_[p], (IsUnit x ∨ IsUnit y ∨ IsUnit z) ∧
    (a : ℚ_[p]) * (↑x : ℚ_[p]) ^ 2 + (b : ℚ_[p]) * (↑y : ℚ_[p]) ^ 2 = (↑z : ℚ_[p]) ^ 2

end PadicDef

end HilbertSymbol

variable (F : Type*) [Field F]

/-- The Hilbert symbol $(a, b)_F \in \{\pm 1\}$ for units of a field $F$:
takes the value $1$ if $ax^2 + by^2 = 1$ has a solution in $F$, and $-1$ otherwise.
This is Definition 10.1 of the textbook (in its general form for a field $F$). -/
noncomputable def hilbertSymbol (a b : Fˣ) : ℤ :=
  if HilbertSymbol.IsSolvable F a b then 1 else -1

