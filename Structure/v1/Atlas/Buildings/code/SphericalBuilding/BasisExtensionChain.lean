/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/BasisExtensionChain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnCommonApartment
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finrank


public section

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- Hypothesis: any finite list of proper non-zero subspaces is simultaneously compatible
with some frame $F$ — i.e.\ admits a simultaneous adapted basis. -/
structure AdaptedBasisHyp where
  adapt : ∀ (subs : List (Submodule k (Vec k n))),
    (∀ V ∈ subs, V ≠ ⊥ ∧ V ≠ ⊤) →
    ∃ F : Frame k n, ∀ V ∈ subs, F.IsCompatible k n V

end GLnBuilding
