/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.TreeNoSepEuler.Part6
import Def.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable


theorem phb_doubleDualShift_latAdj {x y : Site 2} :
    (hypercubicLattice 2).Adj (phb_doubleDualShift x) (phb_doubleDualShift y) ↔
      (hypercubicLattice 2).Adj x y := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_two, phb_doubleDualShift,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring_nf


theorem phb_sharedPrimalEdge_shift_eq_flankFaces {x y : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y) :
    sharedPrimalEdge (phb_doubleDualShift x) (phb_doubleDualShift y) = flankFaces x y := by
  classical
  have hshift : (hypercubicLattice 2).Adj (phb_doubleDualShift x) (phb_doubleDualShift y) :=
    phb_doubleDualShift_latAdj.mpr hxy
  rw [← symPrimal_eq_shared hshift]
  rcases adj_cases hxy with ⟨h0, hy⟩ | ⟨h1, hx⟩
  · unfold symPrimal flankFaces phb_doubleDualShift
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [if_pos (by omega), if_pos h0]
    rcases hy with hxy | hyx
    · rw [show max (x 1 - 1) (y 1 - 1) = y 1 by omega,
          show min (x 1) (y 1) = y 1 by omega]
      congr 1 <;> ext i <;> fin_cases i <;> simp <;> omega
    · rw [show max (x 1 - 1) (y 1 - 1) = x 1 by omega,
          show min (x 1) (y 1) = x 1 by omega]
      congr 1 <;> ext i <;> fin_cases i <;> simp <;> omega
  · unfold symPrimal flankFaces phb_doubleDualShift
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [if_neg (by omega), if_neg (by omega)]
    rcases hx with hxy | hyx
    · rw [show max (x 0 - 1) (y 0 - 1) = y 0 by omega,
          show min (x 0) (y 0) = y 0 by omega, h1, min_self]
      congr 1 <;> ext i <;> fin_cases i <;> simp <;> omega
    · rw [show max (x 0 - 1) (y 0 - 1) = x 0 by omega,
          show min (x 0) (y 0) = x 0 by omega, h1, min_self]
      congr 1 <;> ext i <;> fin_cases i <;> simp <;> omega


theorem phb_flankFaces_mem_faceBoundaryGraph_iff {K : Set (Site 2)} {x y : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y) :
    flankFaces x y ∈ (faceBoundaryGraph K).edgeSet ↔ bdEdge K s(x, y) := by
  constructor
  · intro h
    have him := symPrimalSym_mem_boundaryEdgeSet h
    rw [symPrimalSym_flankFaces hxy] at him
    rw [bdEdge_eq_edgeStraddles, edgeStraddles_iff_mem_boundaryEdgeSet K hxy]
    exact him
  · intro h
    have hmem : s(x, y) ∈ boundaryEdgeSet K := by
      rw [← edgeStraddles_iff_mem_boundaryEdgeSet K hxy, ← bdEdge_eq_edgeStraddles]
      exact h
    exact (flankFacesSym_mem_edgeSet hmem).1


end Lattice
end StatMech
