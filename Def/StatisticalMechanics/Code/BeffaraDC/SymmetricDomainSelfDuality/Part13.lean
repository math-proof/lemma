/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part10
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part8
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

def connectedVAxisPoint : Site 2 := ![0, 0]


def connectedVDomain : SymmetricDomain where
  u₁ := disjointLeftPoint
  v₁ := disjointLeftPoint
  u₂ := disjointRightPoint
  v₂ := disjointRightPoint
  γ₁ := SimpleGraph.Walk.nil
  γ₂ := SimpleGraph.Walk.nil
  isSymm := by
    simp [IsSymmetricPair, disjointLeftPoint, disjointRightPoint]
  G := {connectedVAxisPoint, disjointLeftPoint, disjointRightPoint}
  finite :=
    ((Set.finite_singleton disjointRightPoint).insert disjointLeftPoint).insert
      connectedVAxisPoint
  γ₁_subset := by simp
  γ₂_subset := by simp
  G_symm := by
    ext z
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, (rfl | rfl | rfl), rfl⟩
      · exact Or.inl (by simp [diagReflFun, connectedVAxisPoint])
      · exact Or.inr (Or.inr (by
          simp [diagReflFun, disjointLeftPoint, disjointRightPoint]))
      · exact Or.inr (Or.inl (by
          simp [diagReflFun, disjointLeftPoint, disjointRightPoint]))
    · rintro (rfl | rfl | rfl)
      · refine ⟨connectedVAxisPoint, Or.inl rfl, ?_⟩
        simp [diagReflFun, connectedVAxisPoint]
      · refine ⟨disjointRightPoint, Or.inr (Or.inr rfl), ?_⟩
        simp [diagReflFun, disjointLeftPoint, disjointRightPoint]
      · refine ⟨disjointLeftPoint, Or.inr (Or.inl rfl), ?_⟩
        simp [diagReflFun, disjointLeftPoint, disjointRightPoint]


def connectedVAxis : connectedVDomain.Vertex :=
  ⟨connectedVAxisPoint, by simp [connectedVDomain]⟩


def connectedVLeft : connectedVDomain.Vertex :=
  ⟨disjointLeftPoint, by simp [connectedVDomain]⟩


def connectedVRight : connectedVDomain.Vertex :=
  ⟨disjointRightPoint, by simp [connectedVDomain]⟩


end SymmetricDomain
end
end BeffaraDC
end StatMech
