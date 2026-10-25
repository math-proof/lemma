/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnChainRefinement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnSimultaneousRefinement
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- Hypothesis providing a fixed maximal flag (chain of length $n-1$ of proper non-zero
subspaces) to act as a starting point for refinements. -/
structure BaseFlagHyp where
  base_chain : List (Submodule k (Vec k n))
  base_chain_is_chain : base_chain.IsChain (· < ·)
  base_chain_length : base_chain.length = n - 1
  base_chain_proper : ∀ V ∈ base_chain, V ≠ ⊥ ∧ V ≠ ⊤


/-- Hypothesis: every pair $A < B$ of subspaces with $\dim B \ge \dim A + 2$ admits an
intermediate subspace $W$ with $A < W < B$. -/
structure ChainInsertionHyp where
  fill_gap : ∀ (A B : Submodule k (Vec k n)),
    A < B →
    Module.finrank k ↥A + 2 ≤ Module.finrank k ↥B →
    ∃ W : Submodule k (Vec k n), A < W ∧ W < B

end GLnBuilding
