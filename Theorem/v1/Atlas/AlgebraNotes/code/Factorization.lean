/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Factorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib

public section

namespace Factorization

example : UniqueFactorizationMonoid (Polynomial ℤ) := inferInstance

example (n : ℕ) : UniqueFactorizationMonoid (MvPolynomial (Fin n) ℂ) := inferInstance

end Factorization
