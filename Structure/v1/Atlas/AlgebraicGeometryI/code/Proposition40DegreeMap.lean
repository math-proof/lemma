/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Proposition40DegreeMap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
set_option maxHeartbeats 400000


noncomputable section

open CategoryTheory

namespace Proposition40

universe u v

/-- Abstract input data for Proposition 40: an abelian category `CohSheaf` of "coherent
sheaves" on a smooth complete curve, a predicate selecting locally free objects, a
degree function `degree : CohSheaf → ℤ`, an axiom that every short exact sequence has
the same degree defect as one between locally free objects, and additivity of the
degree on locally free short exact sequences. -/
structure SmoothCompleteCurveCohData where
  /-- The ambient category of coherent sheaves. -/
  CohSheaf : Type u
  [catInst : Category.{v} CohSheaf]
  [abelInst : Abelian CohSheaf]
  /-- The predicate selecting locally free coherent sheaves. -/
  IsLocallyFree : CohSheaf → Prop
  /-- The degree function on coherent sheaves. -/
  degree : CohSheaf → ℤ
  /-- Every short exact sequence admits a "locally free replacement" with the same degree
  defect `deg(X₂) − deg(X₁) − deg(X₃)`. -/
  reduce_to_locally_free :
    ∀ (S : ShortComplex CohSheaf) [Mono S.f] [Epi S.g],
    S.Exact →
    ∃ (S' : ShortComplex CohSheaf),
      Mono S'.f ∧ Epi S'.g ∧ S'.Exact ∧
      IsLocallyFree S'.X₁ ∧ IsLocallyFree S'.X₂ ∧ IsLocallyFree S'.X₃ ∧
      degree S.X₂ - degree S.X₁ - degree S.X₃ =
        degree S'.X₂ - degree S'.X₁ - degree S'.X₃
  /-- Degree is additive on short exact sequences whose terms are all locally free. -/
  locally_free_additive :
    ∀ (S : ShortComplex CohSheaf) [Mono S.f] [Epi S.g],
    S.Exact →
    IsLocallyFree S.X₁ → IsLocallyFree S.X₂ → IsLocallyFree S.X₃ →
    degree S.X₂ = degree S.X₁ + degree S.X₃

end Proposition40
end
