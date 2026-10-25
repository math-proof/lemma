/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FermatsLastTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies
import Def.v1.Atlas.EllipticCurves.code.FermatsLastTheorem.Part2


noncomputable section

namespace FLT

open UniqueFactorizationMonoid

/-- An elliptic curve over `ℚ` is semistable iff its conductor is squarefree. -/
structure Weight2Newform (N : ℕ) where
  coeff : ℕ → ℤ
  coeff_one : coeff 1 = 1
  coeff_mult : ∀ m n : ℕ, Nat.Coprime m n → coeff (m * n) = coeff m * coeff n
  coeff_prime_power : ∀ (p : ℕ) (r : ℕ), Nat.Prime p → ¬(p ∣ N) → r ≥ 1 →
    coeff (p ^ (r + 1)) = coeff p * coeff (p ^ r) - (p : ℤ) * coeff (p ^ (r - 1))

end FLT
end
