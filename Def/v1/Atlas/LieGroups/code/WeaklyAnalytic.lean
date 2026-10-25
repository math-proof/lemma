/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/WeaklyAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.LieGroups.code.HarishChandraFunctor
import Lemma.Set.Dense_KFiniteSubspace.of.IsAdmissible
import Lemma.Submodule.Any_And_All_Eq_GetToMonoidHomAndAll_In_Span.of.IsMaximalCompactSubgroup.IsSemisimpleLieGroupG
import Def.v1.Atlas.LieGroups.code.GKModuleDefs.Part2
import Def.v1.Atlas.LieGroups.code.AnalyticityRegularity.Part2
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Group.Quotient
universe uFw


noncomputable section

set_option autoImplicit false

open scoped Manifold

def ContinuousRep.IsWeaklyAnalytic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F)
    (v : F) : Prop :=
  ∀ (h : F →L[ℂ] ℂ) (g₀ : G),
    AnalyticAt ℝ
      (fun (e : E) =>
        (h (π.toMonoidHom ((chartAt H g₀).symm (I.symm e)) v) : ℂ))
      (I (chartAt H g₀ g₀))

namespace EllipticOperator

def IsEllipticAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (symbolAt : E → ℝ) : Prop :=
  ∀ (p : E), p ≠ 0 → symbolAt p ≠ 0

def IsElliptic
    {X : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ : X → E → ℝ) : Prop :=
  ∀ (x : X), IsEllipticAt (σ x)

end EllipticOperator
end
