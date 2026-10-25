/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Divisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Def.v1.Atlas.EllipticCurves.code.Divisors.Part4


noncomputable section

open Finsupp

variable {P : Type*}

noncomputable section

/-- A smooth projective curve, represented abstractly by a type of points
`Point`, a function field `FunctionField` (a field), and a discrete-valuation
map `val P : FunctionField → WithTop ℤ` at each point `P` satisfying the
standard axioms of a normalized valuation: `val P 0 = ⊤`, `val P 1 = 0`,
`val P (fg) = val P f + val P g`, `val P (f+g) ≥ min (val P f) (val P g)`,
finiteness at nonzero elements, and surjectivity onto `ℤ`. -/
structure SmoothProjectiveCurve where
  Point : Type*
  FunctionField : Type*
  [fieldInst : Field FunctionField]
  val : Point → FunctionField → WithTop ℤ
  val_zero : ∀ P, val P 0 = ⊤
  val_one : ∀ P, val P 1 = 0
  val_mul : ∀ P f g, val P (f * g) = val P f + val P g
  val_add : ∀ P f g, min (val P f) (val P g) ≤ val P (f + g)
  val_ne_top : ∀ P (f : FunctionField), f ≠ 0 → val P f ≠ ⊤
  val_surj : ∀ P (n : ℤ), ∃ f : FunctionField, f ≠ 0 ∧ val P f = ↑n

attribute [instance] SmoothProjectiveCurve.fieldInst

/-- A morphism `C → ℙ¹` from a smooth projective curve, recorded via a chosen
function `f`, its degree, and the (finite) fiber over each point of `ℙ¹`. The
`uniformizerComp Q` represents the uniformizer at `Q ∈ ℙ¹` pulled back to a
function on `C`. -/
structure MorphismToP1 (C : SmoothProjectiveCurve) where
  f : C.FunctionField
  f_ne_zero : f ≠ 0
  deg : ℤ
  deg_pos : 0 < deg
  P1Point : Type*
  uniformizerComp : P1Point → C.FunctionField
  uniformizerComp_ne_zero : ∀ Q, uniformizerComp Q ≠ 0
  fiber : P1Point → Finset C.Point
  mem_fiber_iff : ∀ Q (P : C.Point),
    P ∈ fiber Q ↔ (0 : WithTop ℤ) < C.val P (uniformizerComp Q)

/-- The degree of a morphism `φ : C → ℙ¹` equals the sum, over the points `P` in
the fiber over `Q`, of the valuation `v_P(uniformizerComp Q)`. This is the
content of the degree-fiber formula for morphisms to `ℙ¹`. -/
structure RationalMap (C : SmoothProjectiveCurve) (m : ℕ) where
  coords : Fin m → C.FunctionField
  not_all_zero : ∃ i, coords i ≠ 0

end
end
