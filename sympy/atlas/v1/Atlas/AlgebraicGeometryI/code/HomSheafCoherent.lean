/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/HomSheafCoherent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic

namespace HomSheafCoherent

variable {R : Type*} [CommRing R]

/-- Localization commutes with `Hom` when `M` is finitely presented: the natural map
`S⁻¹ Hom(M, N) → Hom(S⁻¹ M, S⁻¹ N)` is a linear equivalence. -/
noncomputable def hom_localization_equiv
    (M N : Type*) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    [AddCommGroup N] [Module R N]
    (S : Submonoid R) :
    LocalizedModule S (M →ₗ[R] N) ≃ₗ[R]
      (LocalizedModule S M →ₗ[R] LocalizedModule S N) :=
  Module.FinitePresentation.linearEquivMap S

/-- Noetherian version of `hom_localization_equiv`: over a Noetherian ring,
finitely generated implies finitely presented, so the Hom-localization equivalence holds. -/
noncomputable def hom_localization_equiv_noetherian [IsNoetherianRing R]
    (M N : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N]
    (S : Submonoid R) :
    LocalizedModule S (M →ₗ[R] N) ≃ₗ[R]
      (LocalizedModule S M →ₗ[R] LocalizedModule S N) := by
  haveI : Module.FinitePresentation R M :=
    (Module.finitePresentation_iff_finite R M).mpr inferInstance
  exact Module.FinitePresentation.linearEquivMap S
