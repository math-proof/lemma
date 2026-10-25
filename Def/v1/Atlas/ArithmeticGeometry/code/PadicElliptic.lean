/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicElliptic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Monotone.Basic
import Abbrev.v1.Atlas.ArithmeticGeometry.code.PadicElliptic


noncomputable section

open scoped Padic


attribute [local instance] Classical.dec

namespace PadicElliptic

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- Membership predicate for the $n$-th piece $E_n(\mathbb{Q}_p)$ of the $p$-adic filtration:
a point is either the identity, or has $y \ne 0$ and $v_p(x) - v_p(y) \ge n$. -/
def InPadicFiltration (W : WeierstrassCurve ℚ) (n : ℕ)
    (P : PadicPointGroup W (p := p)) : Prop :=
  match P with
  | .zero => True
  | .some x y _ => y ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x - Padic.valuation y

end PadicElliptic
end
