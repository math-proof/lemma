/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveSingletonRowTag.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteFullSources
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveSingletonRowTag


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness.FluxEdgeCopy

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaCurrentSeamEdge_toFinset_eq_matchingSeamSource
    (sites : I -> V) (k : I) :
    (lpReplicaCurrentSeamEdge sites k).toFinset =
      lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) k := by
  have hne : lpReplicaCurrentLeft sites k ≠
      lpReplicaCurrentRight sites k := by
    simp [lpReplicaCurrentLeft, lpReplicaCurrentRight]
  ext x
  simp only [lpReplicaCurrentSeamEdge, Sym2.mem_toFinset, Sym2.mem_iff,
    lpMatchingSeamSource, Finset.mem_symmDiff, Finset.mem_singleton]
  change (x = lpReplicaCurrentLeft sites k ∨
      x = lpReplicaCurrentRight sites k) ↔
    (x = lpReplicaCurrentLeft sites k ∧
        x ≠ lpReplicaCurrentRight sites k) ∨
      (x = lpReplicaCurrentRight sites k ∧
        x ≠ lpReplicaCurrentLeft sites k)
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl ⟨rfl, hne⟩
    · exact Or.inr ⟨rfl, hne.symm⟩
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩)
    · exact Or.inl hx
    · exact Or.inr hx


end
end StatMech.Ising
