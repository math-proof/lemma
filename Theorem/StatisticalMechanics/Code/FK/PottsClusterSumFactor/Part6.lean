/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Def.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part6
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


theorem measurableSet_pottsClusterEqEvent
    (d : Nat) (x : Site d) (F : Finset (Site d)) :
    MeasurableSet (pottsClusterEqEvent d x F) := by
  have heq : pottsClusterEqEvent d x F =
      ⋂ y : Site d, if y ∈ F then
        {omega : ConfigSpace (Sym2 (Site d)) | Connected d omega x y}
      else
        {omega : ConfigSpace (Sym2 (Site d)) | Connected d omega x y}ᶜ := by
    ext omega
    simp only [pottsClusterEqEvent, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h y
      by_cases hy : y ∈ F
      · rw [if_pos hy]
        change Connected d omega x y
        rw [← mem_cluster, h]
        exact hy
      · rw [if_neg hy]
        change ¬Connected d omega x y
        intro hconn
        apply hy
        have hmem : y ∈ cluster d omega x := hconn
        have hmemF : y ∈ (F : Set (Site d)) := by
          rw [← h]
          exact hmem
        simpa using hmemF
    · intro h
      ext y
      specialize h y
      by_cases hy : y ∈ F
      · have hconn : Connected d omega x y := by
          simpa [hy] using h
        exact iff_of_true hconn hy
      · have hnconn : ¬Connected d omega x y := by
          simpa [hy] using h
        exact iff_of_false hnconn hy
  rw [heq]
  apply MeasurableSet.iInter
  intro y
  by_cases hy : y ∈ F
  · rw [if_pos hy]
    exact measurableSet_connected x y
  · rw [if_neg hy]
    exact (measurableSet_connected x y).compl


end StatMech.FK
