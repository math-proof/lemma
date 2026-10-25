/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/VermaModules.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Order.Atoms
import Mathlib.RingTheory.Congruence.Defs
import Def.v1.Atlas.LieGroups.code.VermaModules.Part2


noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

namespace TriangularDecomposition

variable (Δ : TriangularDecomposition R 𝔤)

section UEASubalgHelpers

variable {R : Type*} [CommRing R]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : Type*} [AddCommGroup M] [Module R M]
  [LieRingModule 𝔤 M] [LieModule R 𝔤 M]

theorem IsVermaModule.quotient_by_maximal_irreducible (_hM : IsVermaModule Δ M wt)
    (J : LieSubmodule R 𝔤 M) (hJ_ne_top : J ≠ ⊤)
    (hJ_max : ∀ (N : LieSubmodule R 𝔤 M), N ≠ ⊤ → N ≤ J) :
    LieModule.IsIrreducible R 𝔤 (M ⧸ J) := by

  show IsSimpleOrder (LieSubmodule R 𝔤 (M ⧸ J))

  have : Nontrivial (LieSubmodule R 𝔤 (M ⧸ J)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    apply hJ_ne_top
    rw [eq_top_iff]
    intro m _
    have hmem : (LieSubmodule.Quotient.mk' J) m ∈ (⊤ : LieSubmodule R 𝔤 (M ⧸ J)) := trivial
    rw [← h] at hmem
    rw [LieSubmodule.mem_bot] at hmem
    rwa [LieSubmodule.Quotient.mk_eq_zero] at hmem

  exact {
    eq_bot_or_eq_top := by
      intro N'

      set N := N'.comap (LieSubmodule.Quotient.mk' J) with hN_def

      have hJN : J ≤ N := by
        intro m hm
        show m ∈ N'.comap (LieSubmodule.Quotient.mk' J)
        rw [LieSubmodule.mem_comap]
        rw [(LieSubmodule.Quotient.mk_eq_zero J).mpr hm]
        exact N'.zero_mem

      by_cases hN : N = ⊤
      ·
        right; rw [eq_top_iff]; intro x _
        obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J x
        exact (hN ▸ trivial : m ∈ N)
      ·
        left
        have hNJ : N ≤ J := hJ_max N hN
        rw [eq_bot_iff]; intro x hx
        obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J x
        rw [LieSubmodule.mem_bot]
        exact (LieSubmodule.Quotient.mk_eq_zero J).mpr (hNJ hx) }

end UEASubalgHelpers
end TriangularDecomposition
end
