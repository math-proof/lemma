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
import Theorem.v1.Atlas.LieGroups.code.WeaklyAnalytic
universe uFw


noncomputable section

set_option autoImplicit false

open scoped Manifold

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

end
