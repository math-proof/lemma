module
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
public import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part15


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareNeighborSite_mem (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    fkIsingSquareNeighborSite u.1 d ∈ box 2 n := by
  intro i
  have b0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have b1 := fkIsingSquareVertex_coordinate_bounds n u 1
  have hb : -(n : Int) ≤ fkIsingSquareNeighborSite u.1 d i ∧
      fkIsingSquareNeighborSite u.1 d i ≤ (n : Int) := by
    cases d <;> fin_cases i <;>
      simp [fkIsingSquareNeighborSite, Pi.add_apply,
        fkIsingSquareDirectionAvailable] at hd ⊢ <;>
      omega
  have ha : |fkIsingSquareNeighborSite u.1 d i| ≤ (n : Int) :=
    abs_le.mpr hb
  rw [Int.abs_eq_natAbs] at ha
  exact_mod_cast ha


end
end StatMech.Universality
