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
import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnBaseFlag.Part2


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- The standard flag chain has length $n-1$. -/
theorem stdFlagChain_length : (stdFlagChain k n).length = n - 1 :=
  List.length_ofFn

/-- The standard flag chain is strictly increasing. -/
theorem stdFlagChain_isChain :
    (stdFlagChain k n).IsChain (· < ·) := by
  rw [stdFlagChain, List.isChain_iff_pairwise, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp [List.length_ofFn] at hi hj
  rw [List.getElem_ofFn, List.getElem_ofFn]
  exact stdFlagSubspace_strictMono k n (Fin.mk_lt_mk.mpr hij)

/-- Every subspace in the standard flag chain is proper and non-zero. -/
theorem stdFlagChain_proper :
    ∀ V ∈ stdFlagChain k n, V ≠ ⊥ ∧ V ≠ ⊤ := by
  intro V hV
  rw [stdFlagChain, List.mem_ofFn] at hV
  obtain ⟨i, rfl⟩ := hV
  exact ⟨stdFlagSubspace_ne_bot k n i, stdFlagSubspace_ne_top k n i⟩


end GLnBuilding
