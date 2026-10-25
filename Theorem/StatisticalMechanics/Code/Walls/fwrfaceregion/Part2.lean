/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
import Theorem.StatisticalMechanics.Code.Walls.ceosimplecycle
import Theorem.StatisticalMechanics.Code.Walls.dowdartwinding
import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
import Def.StatisticalMechanics.Code.Walls.fwrfaceregion
open Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem fwr_faceInside_mk {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (x y : ℤ) :
    fwr_faceInside Vc (![x, y] : Site 2)
      ↔ ¬ Even (jec_rayCount (![x + 1, y + 1] : Site 2) Vc) := by
  unfold fwr_faceInside
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]


theorem fwr_paritySwap (P Q : Prop) :
    ((¬ P) ↔ ¬ ¬ Q) ↔ ((¬ Q) ↔ ¬ ¬ P) := by
  constructor <;> intro h <;>
    · by_cases hp : P <;> by_cases hq : Q <;> simp_all


theorem fwr_faceCutFlip_aux_h {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {c' d' : Site 2} (hcd : (hypercubicLattice 2).Adj c' d') :
    ((¬ Even (jec_rayCount c' Vc)) ↔ ¬ ¬ Even (jec_rayCount d' Vc))
      ↔ Odd (Vc.edges.count (rpc_crossEdge c' d')) := by
  have h := rpc_crossFlip Vc hcd
  rw [bdEdge_mk, jec_mem_leftRegion, jec_mem_leftRegion] at h
  exact h


theorem fwr_faceCutFlip_aux_v {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {c' d' : Site 2} (hcd : (hypercubicLattice 2).Adj c' d') :
    ((¬ Even (jec_rayCount c' Vc)) ↔ ¬ ¬ Even (jec_rayCount d' Vc))
      ↔ Odd (Vc.edges.count (rpc_crossEdge c' d')) :=
  fwr_faceCutFlip_aux_h Vc hcd


theorem fwr_faceCutFlip {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {c d : Site 2} (hcd : (hypercubicLattice 2).Adj c d) :
    (fwr_faceInside Vc c ↔ ¬ fwr_faceInside Vc d)
      ↔ Odd (Vc.edges.count (sharedPrimalEdge c d)) := by
  classical
  
  set x := c 0 with hx
  set y := c 1 with hy
  have hc : c = ![x, y] := by funext i; fin_cases i <;> rfl
  have hcd' := hcd
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hcd'
  
  by_cases h0 : d 0 = c 0 + 1
  · 
    have hd0 : d 0 = x + 1 := by rw [hx]; omega
    have hd1 : d 1 = y := by rw [hy]; omega
    have hd : d = ![x + 1, y] := by
      funext i; fin_cases i
      · simpa using hd0
      · simpa using hd1
    have hc1 : (hypercubicLattice 2).Adj (![x + 1, y + 1] : Site 2) (![x + 2, y + 1] : Site 2) := by
      simp [hypercubicLattice_adj, Fin.sum_univ_two]
    rw [hc, hd, fwr_faceInside_mk, fwr_faceInside_mk, fwr_sharedEdge_eq_crossEdge_horiz]
    rw [show (x + 1 + 1 : ℤ) = x + 2 by ring]
    rw [← fwr_faceCutFlip_aux_h Vc hc1]
  · by_cases h0' : c 0 = d 0 + 1
    · 
      have hd0 : d 0 = x - 1 := by rw [hx]; omega
      have hd1 : d 1 = y := by rw [hy]; omega
      have hd : d = ![x - 1, y] := by
        funext i; fin_cases i
        · simpa using hd0
        · simpa using hd1
      have hc1 : (hypercubicLattice 2).Adj (![(x - 1) + 1, y + 1] : Site 2)
          (![(x - 1) + 2, y + 1] : Site 2) := by
        rw [hypercubicLattice_adj, Fin.sum_univ_two]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
      have hshare : sharedPrimalEdge c d = sharedPrimalEdge (![x - 1, y] : Site 2)
          (![(x - 1) + 1, y] : Site 2) := by
        rw [hc, hd, sharedPrimalEdge_comm_of_adj (by
          rw [hypercubicLattice_adj, Fin.sum_univ_two]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega)]
        congr 2 <;> omega
      rw [hshare, fwr_sharedEdge_eq_crossEdge_horiz, hc, hd,
        fwr_faceInside_mk, fwr_faceInside_mk]
      have := fwr_faceCutFlip_aux_h Vc hc1
      
      rw [show ((x - 1) + 1 : ℤ) = x by ring, show ((x - 1) + 2 : ℤ) = x + 1 by ring] at this ⊢
      rw [← this]
      exact fwr_paritySwap _ _
    · 
      have hveq0 : d 0 = c 0 := by omega
      by_cases h1 : d 1 = c 1 + 1
      · 
        have hd0 : d 0 = x := by rw [hx]; exact hveq0
        have hd1 : d 1 = y + 1 := by rw [hy]; omega
        have hd : d = ![x, y + 1] := by
          funext i; fin_cases i
          · simpa using hd0
          · simpa using hd1
        have hc1 : (hypercubicLattice 2).Adj (![x + 1, y + 1] : Site 2)
            (![x + 1, y + 2] : Site 2) := by
          simp [hypercubicLattice_adj, Fin.sum_univ_two]
        rw [hc, hd, fwr_faceInside_mk, fwr_faceInside_mk, fwr_sharedEdge_eq_crossEdge_vert]
        rw [show (y + 1 + 1 : ℤ) = y + 2 by ring]
        rw [← fwr_faceCutFlip_aux_v Vc hc1]
      · 
        have hd0 : d 0 = x := by rw [hx]; exact hveq0
        have hd1 : d 1 = y - 1 := by rw [hy]; omega
        have hd : d = ![x, y - 1] := by
          funext i; fin_cases i
          · simpa using hd0
          · simpa using hd1
        have hc1 : (hypercubicLattice 2).Adj (![x + 1, (y - 1) + 1] : Site 2)
            (![x + 1, (y - 1) + 2] : Site 2) := by
          rw [hypercubicLattice_adj, Fin.sum_univ_two]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
        have hshare : sharedPrimalEdge c d = sharedPrimalEdge (![x, y - 1] : Site 2)
            (![x, (y - 1) + 1] : Site 2) := by
          rw [hc, hd, sharedPrimalEdge_comm_of_adj (by
            rw [hypercubicLattice_adj, Fin.sum_univ_two]
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega)]
          congr 2
          funext i; fin_cases i <;>
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] <;> omega
        rw [hshare, fwr_sharedEdge_eq_crossEdge_vert, hc, hd,
          fwr_faceInside_mk, fwr_faceInside_mk]
        have := fwr_faceCutFlip_aux_v Vc hc1
        rw [show ((y - 1) + 1 : ℤ) = y by ring, show ((y - 1) + 2 : ℤ) = y + 1 by ring] at this ⊢
        rw [← this]
        exact fwr_paritySwap _ _


theorem fwr_faceCutMatch_of_nodup {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hnd : Vc.edges.Nodup) {c d : Site 2} (hcd : (hypercubicLattice 2).Adj c d) :
    (fwr_faceInside Vc c ↔ ¬ fwr_faceInside Vc d) ↔ sharedPrimalEdge c d ∈ Vc.edges := by
  rw [fwr_faceCutFlip Vc hcd]
  exact dow_odd_count_iff_mem_of_nodup hnd _


theorem fwr_jedCutSet_match_of_nodup {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hnd : Vc.edges.Nodup) {c d : Site 2} (hcd : (hypercubicLattice 2).Adj c d) :
    sharedPrimalEdge c d ∈ jed_cutSet (fwr_faceInside Vc) ↔ sharedPrimalEdge c d ∈ Vc.edges := by
  rw [jed_mem_cutSet_iff (fwr_faceInside Vc) hcd]
  
  exact fwr_faceCutMatch_of_nodup Vc hnd hcd


theorem fwr_primalWalkBoundsFaceRegion_of_nodup {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (hnd : Vc.edges.Nodup)
    {u v : Site 2} (huv : (hypercubicLattice 2).Adj u v) :
    s(u, v) ∈ Vc.edges ↔ s(u, v) ∈ jed_cutSet (fwr_faceInside Vc) := by
  obtain ⟨f0, g0, hfg, hshared⟩ := jfc_flankingFaces huv
  rw [← hshared]
  exact (fwr_jedCutSet_match_of_nodup Vc hnd hfg).symm


end Walls
end StatMech
