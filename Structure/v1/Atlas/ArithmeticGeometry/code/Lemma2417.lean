/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Lemma2417.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Tactic


noncomputable section

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

namespace Lemma2417

/-- The condition that a (projective-like) point $(x, z)$ on the dehomogenized Weierstrass curve
$z = x^3 + a_4 x z^2 + a_6 z^3$ lies in the $n$-th piece $E_n$ of the $p$-adic filtration:
$p^n \mid x$ and $p^{3n} \mid z$. -/
structure IsInEn (a₄ a₆ : ℤ_[p]) (n : ℕ) (x z : ℤ_[p]) : Prop where
  on_curve : z = x ^ 3 + a₄ * x * z ^ 2 + a₆ * z ^ 3
  val_x : (p : ℤ_[p]) ^ n ∣ x
  val_z : (p : ℤ_[p]) ^ (3 * n) ∣ z

end Lemma2417
end
