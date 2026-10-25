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
import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnBaseFlag


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- The chosen generators of `stdFlagSubspace k n i` are linearly independent. -/
theorem stdFlagSubspace_generators_linIndep (i : Fin (n - 1)) :
    LinearIndependent k (fun (j : Fin (i.val + 1)) =>
      (Pi.basisFun k (Fin n)) (⟨j.val, by omega⟩ : Fin n)) := by
  apply (Pi.basisFun k (Fin n)).linearIndependent.comp
  intro a b hab
  exact Fin.ext (by simp [Fin.ext_iff] at hab; exact hab)

/-- $\dim_k(\mathrm{stdFlagSubspace}\ k\ n\ i) = i + 1$. -/
theorem stdFlagSubspace_finrank (i : Fin (n - 1)) :
    Module.finrank k ↥(stdFlagSubspace k n i) = i.val + 1 := by
  rw [stdFlagSubspace, finrank_span_eq_card (stdFlagSubspace_generators_linIndep k n i)]
  simp [Fintype.card_fin]


/-- Standard flag subspaces are monotone in the index. -/
theorem stdFlagSubspace_mono {i j : Fin (n - 1)} (h : i ≤ j) :
    stdFlagSubspace k n i ≤ stdFlagSubspace k n j := by
  apply Submodule.span_mono
  intro x hx
  obtain ⟨m, rfl⟩ := hx
  exact ⟨⟨m.val, by omega⟩, by simp⟩

/-- Standard flag subspaces are strictly monotone in the index. -/
theorem stdFlagSubspace_strictMono {i j : Fin (n - 1)} (h : i < j) :
    stdFlagSubspace k n i < stdFlagSubspace k n j := by
  apply Submodule.lt_of_le_of_finrank_lt_finrank (stdFlagSubspace_mono k n h.le)
  rw [stdFlagSubspace_finrank, stdFlagSubspace_finrank]
  omega


/-- Each standard flag subspace is non-zero. -/
theorem stdFlagSubspace_ne_bot (i : Fin (n - 1)) :
    stdFlagSubspace k n i ≠ ⊥ := by
  intro h
  have h1 := stdFlagSubspace_finrank k n i
  rw [h] at h1
  simp at h1

/-- Each standard flag subspace is a proper subspace of $k^n$. -/
theorem stdFlagSubspace_ne_top (i : Fin (n - 1)) :
    stdFlagSubspace k n i ≠ ⊤ := by
  intro h
  have h1 := stdFlagSubspace_finrank k n i
  rw [h] at h1
  simp [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h1
  omega


end GLnBuilding
