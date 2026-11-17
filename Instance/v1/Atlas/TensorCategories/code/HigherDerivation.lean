/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Class.v1.Atlas.TensorCategories.code.HigherDerivation

@[expose] public section

set_option maxHeartbeats 800000

universe v u w


namespace TensorCategories

/-- Any field of characteristic zero satisfies `HasHigherDerivationContradiction`, via the
vanishing theorem `higher_derivation_vanishes`. -/
instance instHasHigherDerivationContradiction (k : Type w) [Field k] [CharZero k] :
    HasHigherDerivationContradiction k where
  higher_derivation_vanishes := fun _ _ _ _ _ hds =>
    hds.higher_derivation_vanishes

end TensorCategories
