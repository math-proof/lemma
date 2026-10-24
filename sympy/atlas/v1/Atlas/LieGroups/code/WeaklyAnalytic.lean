/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/WeaklyAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.HarishChandraFunctor
import Lemma.Set.Dense_KFiniteSubspace.of.IsAdmissible
import Lemma.Submodule.Any_And_All_Eq_GetToMonoidHomAndAll_In_Span.of.IsMaximalCompactSubgroup.IsSemisimpleLieGroupG
import sympy.atlas.v1.Atlas.LieGroups.code.GKModuleDefs
import sympy.atlas.v1.Atlas.LieGroups.code.AnalyticityRegularity
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

open EllipticOperator in
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (h : IsEllipticAt f)
    (p : E) (hp : p ≠ 0) : f p ≠ 0 := h p hp

def ContinuousRep.IsFiniteLength
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (π : ContinuousRep G V) : Prop :=
  ∃ (n : ℕ) (chain : Fin (n + 1) → Submodule ℂ V),
    chain ⟨0, Nat.zero_lt_succ n⟩ = ⊥ ∧
    chain ⟨n, Nat.lt_succ_iff.mpr (le_refl n)⟩ = ⊤ ∧
    (∀ (i : Fin n), chain i.castSucc < chain i.succ) ∧
    (∀ (i : Fin n), π.IsInvariantSubspace (chain i.castSucc)) ∧
    (∀ (i : Fin n), π.IsInvariantSubspace (chain i.succ)) ∧


    (∀ (i : Fin n) (W : Submodule ℂ V), π.IsInvariantSubspace W →
      chain i.castSucc ≤ W → W ≤ chain i.succ →
      W = chain i.castSucc ∨ W = chain i.succ)
