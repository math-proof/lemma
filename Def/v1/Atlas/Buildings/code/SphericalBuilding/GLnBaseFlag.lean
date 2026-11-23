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

@[expose] public section

namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- The $i$-th subspace of the standard flag: the span of the first $i+1$ standard basis
vectors in $k^n$. -/
noncomputable def stdFlagSubspace (i : Fin (n - 1)) : Submodule k (Vec k n) :=
  Submodule.span k (Set.range (fun (j : Fin (i.val + 1)) =>
    (Pi.basisFun k (Fin n)) (⟨j.val, by omega⟩ : Fin n)))

end GLnBuilding
