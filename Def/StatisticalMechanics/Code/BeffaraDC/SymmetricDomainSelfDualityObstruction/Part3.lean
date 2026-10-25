/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part12
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDualityObstruction.Part2
open Set SimpleGraph
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

namespace SymmetricDomain

noncomputable section

def separatedSymmetricDomain : SymmetricDomain where
  u₁ := separatedSiteOne
  v₁ := separatedSiteOne
  u₂ := separatedSiteTwo
  v₂ := separatedSiteTwo
  γ₁ := SimpleGraph.Walk.nil
  γ₂ := SimpleGraph.Walk.nil
  isSymm := by
    simp [IsSymmetricPair]
  G := {separatedSiteOne, separatedSiteTwo}
  finite := Set.toFinite _
  γ₁_subset := by simp
  γ₂_subset := by simp
  G_symm := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨separatedSiteTwo, by simp, by simp⟩
      · exact ⟨separatedSiteOne, by simp, by simp⟩


end
end SymmetricDomain
end BeffaraDC
end StatMech
