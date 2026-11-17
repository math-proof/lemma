module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Theorem.v1.Atlas.TensorCategories.code.HigherDerivation
public section

set_option maxHeartbeats 800000

universe v u w


namespace TensorCategories

/-- Typeclass packaging the vanishing of `χ 1` for every higher derivation system on every
finite-dimensional `k`-algebra, used as a hypothesis in higher-level results. -/
class HasHigherDerivationContradiction (k : Type w) [Field k] [CharZero k] : Prop where
  higher_derivation_vanishes :
    ∀ (A : Type w) [Ring A] [Algebra k A] [FiniteDimensional k A]
      (ε : A →ₐ[k] k) (hds : HigherDerivationSystem k A ε),
      hds.χ 1 = 0

end TensorCategories
