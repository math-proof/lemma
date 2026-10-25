/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.Part7


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareBoundaryFullFace_neighborFinset (n : Nat)
    (c : FKIsingSquareFullFaceNode n)
    (heast : c.1.1 + 1 < 2 * n)
    (hnorth : c.2.1 + 1 < 2 * n)
    (hwest : 0 < c.1.1) (hsouth : 0 < c.2.1)
    [Fintype ↑((fkIsingSquareFullFaceGraph n).neighborSet c)] :
    (fkIsingSquareFullFaceGraph n).neighborFinset c =
      {faceEastNeighbor n c heast, faceNorthNeighbor n c hnorth,
        faceWestNeighbor n c hwest, faceSouthNeighbor n c hsouth} := by
  ext q
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
    Finset.mem_singleton]
  change ((c.1 = q.1 ∧ (c.2.1 + 1 = q.2.1 ∨ q.2.1 + 1 = c.2.1)) ∨
      (c.2 = q.2 ∧ (c.1.1 + 1 = q.1.1 ∨ q.1.1 + 1 = c.1.1))) ↔ _
  constructor
  · rintro (⟨hx, hy | hy⟩ | ⟨hy, hx | hx⟩)
    · right; left
      apply Prod.ext
      · exact hx.symm
      · apply Fin.ext
        exact hy.symm
    · right; right; right
      apply Prod.ext
      · exact hx.symm
      · apply Fin.ext
        simp [faceSouthNeighbor]
        omega
    · left
      apply Prod.ext
      · apply Fin.ext
        exact hx.symm
      · exact hy.symm
    · right; right; left
      apply Prod.ext
      · apply Fin.ext
        simp [faceWestNeighbor]
        omega
      · exact hy.symm
  · rintro (rfl | rfl | rfl | rfl)
    · exact Or.inr ⟨rfl, Or.inl rfl⟩
    · exact Or.inl ⟨rfl, Or.inl rfl⟩
    · exact Or.inr ⟨rfl, Or.inr (by simp [faceWestNeighbor]; omega)⟩
    · exact Or.inl ⟨rfl, Or.inr (by simp [faceSouthNeighbor]; omega)⟩

end
end StatMech.Universality
