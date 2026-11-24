module
public import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnChainRefinement.Part2
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.GLnBaseFlag.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnBaseFlag.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- The standard flag witnesses the existence of a `BaseFlagHyp k n`, providing a fixed
maximal flag to which we may refine arbitrary subspaces. -/
noncomputable def baseFlagHyp : BaseFlagHyp k n where
  base_chain := stdFlagChain k n
  base_chain_is_chain := stdFlagChain_isChain k n
  base_chain_length := stdFlagChain_length k n
  base_chain_proper := stdFlagChain_proper k n

end GLnBuilding
