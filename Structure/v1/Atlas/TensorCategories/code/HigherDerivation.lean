/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite
set_option maxHeartbeats 800000

universe v u w


namespace TensorCategories

section Ext1UnitVanishing

/-- A higher derivation system on a `k`-algebra `A` augmented by `ε : A →ₐ[k] k`: a sequence of
`k`-linear functionals `χ n : A → k` with `χ 0 = ε` and the Leibniz-type product formula
`χ_n(ab) = ∑_j (n choose j) χ_j(a) χ_{n-j}(b)`. Used to prove vanishing of higher derivations
on finite-dimensional algebras in characteristic zero. -/
structure HigherDerivationSystem (k : Type w) [Field k] (A : Type w) [Ring A] [Algebra k A]
    (ε : A →ₐ[k] k) where
  χ : ℕ → (A →ₗ[k] k)
  χ_zero : χ 0 = ε.toLinearMap
  χ_mul : ∀ (n : ℕ) (a b : A),
    χ n (a * b) = ∑ j ∈ Finset.range (n + 1),
      (n.choose j : k) * χ j a * χ (n - j) b

end Ext1UnitVanishing
end TensorCategories
