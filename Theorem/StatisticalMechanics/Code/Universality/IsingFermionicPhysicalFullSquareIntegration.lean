/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDiamondIntegration.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegration


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareFullRadialNodeCoordinate_mem_diamond
    (n : Nat) (z : FKIsingSquareFullRadialNode n) :
    FKIsingSquareFullDiamond n
      (fkIsingSquareFullRadialNodeCoordinate n z) := by
  cases z with
  | inl x =>
      have hx0 := fkIsingSquareVertex_coordinate_bounds n x 0
      have hx1 := fkIsingSquareVertex_coordinate_bounds n x 1
      simp [FKIsingSquareFullDiamond,
        fkIsingSquareFullRadialNodeCoordinate,
        fkIsingSquareFullVertexCoordinate]
      omega
  | inr c =>
      have hc := fkIsingSquareInteriorCellKey_interior n c
      simp [fkIsingSquareInteriorFaceKey] at hc
      simp [FKIsingSquareFullDiamond,
        fkIsingSquareFullRadialNodeCoordinate,
        fkIsingSquareFullFaceCoordinate]
      omega

theorem natAbs_le_of_int_bounds {n : Nat} {z : Int}
    (h0 : -(n : Int) ≤ z) (h1 : z ≤ (n : Int)) : z.natAbs ≤ n := by
  have h : |z| ≤ (n : Int) := abs_le.mpr ⟨h0, h1⟩
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

theorem fkIsingSquareFull_exists_node_of_mem_diamond
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamond n q) :
    ∃ z : FKIsingSquareFullRadialNode n,
      fkIsingSquareFullRadialNodeCoordinate n z = q := by
  rcases hq with ⟨hsum0, hsum1, hdiff0, hdiff1⟩
  rcases (q.1 + q.2).even_or_odd with heven | hodd
  · rcases heven with ⟨a, ha⟩
    let b : Int := q.1 - a
    have ha0 : -(n : Int) ≤ a := by omega
    have ha1 : a ≤ (n : Int) := by omega
    have hb0 : -(n : Int) ≤ b := by
      dsimp [b]
      omega
    have hb1 : b ≤ (n : Int) := by
      dsimp [b]
      omega
    let x : FKIsingSquareFullVertexNode n :=
      ⟨![a, b], by
        intro k
        fin_cases k
        · exact natAbs_le_of_int_bounds ha0 ha1
        · exact natAbs_le_of_int_bounds hb0 hb1⟩
    refine ⟨Sum.inl x, ?_⟩
    apply Prod.ext <;>
      simp [fkIsingSquareFullRadialNodeCoordinate,
        fkIsingSquareFullVertexCoordinate, x, b] <;>
      omega
  · rcases hodd with ⟨a, ha⟩
    let b : Int := q.1 - a - 1
    have ha0 : -(n : Int) ≤ a := by omega
    have ha1 : a < (n : Int) := by omega
    have hb0 : -(n : Int) ≤ b := by
      dsimp [b]
      omega
    have hb1 : b < (n : Int) := by
      dsimp [b]
      omega
    have hp : fkIsingSquareInteriorFaceKey n (a, b) := by
      exact ⟨ha0, ha1, hb0, hb1⟩
    let c : FKIsingSquareFullFaceNode n :=
      fkIsingSquareFullFaceOfKey n (a, b) hp
    refine ⟨Sum.inr c, ?_⟩
    apply Prod.ext <;>
      simp [fkIsingSquareFullRadialNodeCoordinate,
        fkIsingSquareFullFaceCoordinate, c, b] <;>
      omega

end
end StatMech.Universality
