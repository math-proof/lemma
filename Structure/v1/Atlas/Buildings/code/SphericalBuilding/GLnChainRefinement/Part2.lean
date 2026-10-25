/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnChainRefinement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnSimultaneousRefinement
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnChainRefinement


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- Hypothesis: a proper subspace $V$ can be inserted into any maximal flag to produce a new
maximal flag containing both the original chain and $V$. -/
structure FlagInsertionHyp where
  insert : ∀ (chain : List (Submodule k (Vec k n)))
    (V : Submodule k (Vec k n)),
    chain.IsChain (· < ·) →
    chain.length = n - 1 →
    (∀ W ∈ chain, W ≠ ⊥ ∧ W ≠ ⊤) →
    V ≠ ⊥ →
    V ≠ ⊤ →
    ∃ (chain' : List (Submodule k (Vec k n))),
      V ∈ chain' ∧
      (∀ W ∈ chain, W ∈ chain') ∧
      chain'.IsChain (· < ·) ∧
      chain'.length = n - 1 ∧
      (∀ W ∈ chain', W ≠ ⊥ ∧ W ≠ ⊤)


end GLnBuilding
