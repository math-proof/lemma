/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def faceSWVertex (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    FKIsingSquareFullVertexNode n := by
  let p := fkIsingSquareInteriorCellKey n c
  have hp := fkIsingSquareInteriorCellKey_interior n c
  change -(n : Int) ≤ p.1 ∧ p.1 < (n : Int) ∧
    -(n : Int) ≤ p.2 ∧ p.2 < (n : Int) at hp
  refine ⟨![p.1, p.2], ?_⟩
  intro k
  fin_cases k
  · exact natAbs_le_of_bounds hp.1 hp.2.1.le
  · exact natAbs_le_of_bounds hp.2.2.1 hp.2.2.2.le

def faceSEVertex (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    FKIsingSquareFullVertexNode n := by
  let p := fkIsingSquareInteriorCellKey n c
  have hp := fkIsingSquareInteriorCellKey_interior n c
  change -(n : Int) ≤ p.1 ∧ p.1 < (n : Int) ∧
    -(n : Int) ≤ p.2 ∧ p.2 < (n : Int) at hp
  refine ⟨![p.1 + 1, p.2], ?_⟩
  intro k
  fin_cases k
  · change (p.1 + 1).natAbs ≤ n
    exact natAbs_le_of_bounds (by omega) (by omega)
  · exact natAbs_le_of_bounds hp.2.2.1 hp.2.2.2.le

def faceNWVertex (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    FKIsingSquareFullVertexNode n := by
  let p := fkIsingSquareInteriorCellKey n c
  have hp := fkIsingSquareInteriorCellKey_interior n c
  change -(n : Int) ≤ p.1 ∧ p.1 < (n : Int) ∧
    -(n : Int) ≤ p.2 ∧ p.2 < (n : Int) at hp
  refine ⟨![p.1, p.2 + 1], ?_⟩
  intro k
  fin_cases k
  · exact natAbs_le_of_bounds hp.1 hp.2.1.le
  · change (p.2 + 1).natAbs ≤ n
    exact natAbs_le_of_bounds (by omega) (by omega)

def faceNEVertex (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    FKIsingSquareFullVertexNode n := by
  let p := fkIsingSquareInteriorCellKey n c
  have hp := fkIsingSquareInteriorCellKey_interior n c
  change -(n : Int) ≤ p.1 ∧ p.1 < (n : Int) ∧
    -(n : Int) ≤ p.2 ∧ p.2 < (n : Int) at hp
  refine ⟨![p.1 + 1, p.2 + 1], ?_⟩
  intro k
  fin_cases k
  · change (p.1 + 1).natAbs ≤ n
    exact natAbs_le_of_bounds (by omega) (by omega)
  · change (p.2 + 1).natAbs ≤ n
    exact natAbs_le_of_bounds (by omega) (by omega)

end
end StatMech.Universality
