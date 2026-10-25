/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/RefinementDimJumps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.SchreierRefinement
import Lemma.Fin.SchreierCell_0.eq.SpacesSubVal1.of.GtVal_0
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.ModularLattice


namespace GLnBuilding

variable {k : Type*} [Field k] {n : ℕ}

/-- A **strict flag**: a complete flag $\sigma$ in which each subspace $V_j$ has dimension
exactly $j$, i.e., $\dim V_j = j$ for all $j$. -/
def CompleteFlag.IsStrictFlag (σ : CompleteFlag k n) : Prop :=
  ∀ j : Fin (n + 1), Module.finrank k ↥(σ.spaces j) = j.val

end GLnBuilding
