/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnBaseFlag.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnChainRefinement.Part2
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.GLnBaseFlag


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- The complete standard flag in $k^n$ as a list of subspaces of length $n-1$. -/
noncomputable def stdFlagChain : List (Submodule k (Vec k n)) :=
  List.ofFn (stdFlagSubspace k n)

end GLnBuilding
