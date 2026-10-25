/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsclosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.binsinsertion.Part7
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation
open StatMech.Ising StatMech.IsingFK


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 20000


theorem bins_connected_of_walk_edges_open {x y : Site 2}
    (P : (hypercubicLattice 2).Walk x y) (omega : ConfigSpace (Sym2 (Site 2)))
    (hopen : forall e, e ∈ P.edges -> omega e = true) : Connected 2 omega x y := by
  induction P with
  | nil => exact ⟨Walk.nil⟩
  | @cons x y z hxy P ih =>
      apply (IsOpenEdge.connected (ω := omega) (x := x) (y := y) ?_).trans
        (ih (fun e he => hopen e (by simp [he])))
      exact ⟨hxy, hopen s(x, y) (by simp)⟩


theorem bins_cylinder_value {I : Finset (Sym2 (Site 2))}
    {eta : ConfigSpace (Subtype fun e => e ∈ I)} {omega : ConfigSpace (Sym2 (Site 2))}
    (hcyl : omega ∈ cylinder I ({eta} : Set (ConfigSpace (Subtype fun e => e ∈ I))))
    (e : Sym2 (Site 2)) (he : e ∈ I) : omega e = eta ⟨e, he⟩ := by
  rw [MeasureTheory.mem_cylinder, Set.mem_singleton_iff] at hcyl
  exact congrFun hcyl ⟨e, he⟩


theorem bins_corridors_of_same_side (n : ℕ) (hn : 1 ≤ n)
    (v1 v2 v3 : Site 2) (hv1 : v1 ∈ box 2 n) (hv2 : v2 ∈ box 2 n)
    (hv3 : v3 ∈ box 2 n) (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3)
    (hside :
      (v1 0 = (n : ℤ) ∧ v2 0 = (n : ℤ) ∧ v3 0 = (n : ℤ)) ∨
      (v1 0 = -(n : ℤ) ∧ v2 0 = -(n : ℤ) ∧ v3 0 = -(n : ℤ)) ∨
      (v1 1 = (n : ℤ) ∧ v2 1 = (n : ℤ) ∧ v3 1 = (n : ℤ)) ∨
      (v1 1 = -(n : ℤ) ∧ v2 1 = -(n : ℤ) ∧ v3 1 = -(n : ℤ))) :
    bcor_Corridors n v1 v2 v3 := by
  rw [mem_box] at hv1 hv2 hv3
  rcases hside with hr | hl | ht | hb
  · have h := bcor_corridors_same_right_of_distinct n hn (v1 1) (v2 1) (v3 1)
      (hv1 1) (hv2 1) (hv3 1)
      (fun h => h12 (by ext q; fin_cases q <;> simp_all))
      (fun h => h13 (by ext q; fin_cases q <;> simp_all))
      (fun h => h23 (by ext q; fin_cases q <;> simp_all))
    convert h using 1 <;> ext q <;> fin_cases q <;> simp_all
  · have h := bcor_corridors_same_right_of_distinct n hn (-v1 1) (-v2 1) (-v3 1)
      (by simpa using hv1 1) (by simpa using hv2 1) (by simpa using hv3 1)
      (by intro h; apply h12; ext q <;> fin_cases q <;> simp_all)
      (by intro h; apply h13; ext q <;> fin_cases q <;> simp_all)
      (by intro h; apply h23; ext q <;> fin_cases q <;> simp_all)
    have hh := bcor_corridors_rot90_iterate 2 h
    convert hh using 1 <;> ext q <;> fin_cases q <;>
      simp [Function.iterate_succ_apply', rot90Fun_apply] <;> omega
  · have h := bcor_corridors_same_right_of_distinct n hn (-v1 0) (-v2 0) (-v3 0)
      (by simpa using hv1 0) (by simpa using hv2 0) (by simpa using hv3 0)
      (by intro h; apply h12; ext q <;> fin_cases q <;> simp_all)
      (by intro h; apply h13; ext q <;> fin_cases q <;> simp_all)
      (by intro h; apply h23; ext q <;> fin_cases q <;> simp_all)
    have hh := bcor_corridors_rot90 h
    convert hh using 1 <;> ext q <;> fin_cases q <;> simp [rot90Fun_apply] <;> omega
  · have h := bcor_corridors_same_right_of_distinct n hn (v1 0) (v2 0) (v3 0)
      (hv1 0) (hv2 0) (hv3 0)
      (by intro h; apply h12; ext q <;> fin_cases q <;> simp_all)
      (by intro h; apply h13; ext q <;> fin_cases q <;> simp_all)
      (by intro h; apply h23; ext q <;> fin_cases q <;> simp_all)
    have hh := bcor_corridors_rot90_iterate 3 h
    convert hh using 1 <;> ext q <;> fin_cases q <;>
      simp [Function.iterate_succ_apply', rot90Fun_apply] <;> omega


end StatMech.Walls
