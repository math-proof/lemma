/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnBaseFlag.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnChainRefinement.Part2
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.GLnBaseFlag

@[expose] public section

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- The complete standard flag in $k^n$ as a list of subspaces of length $n-1$. -/
noncomputable def stdFlagChain : List (Submodule k (Vec k n)) :=
  List.ofFn (stdFlagSubspace k n)

end GLnBuilding
