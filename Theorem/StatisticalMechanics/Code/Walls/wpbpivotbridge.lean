/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wcddefectbridge.Part5
import Theorem.StatisticalMechanics.Code.Walls.jc5_singlecycle.Part2
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedProof
open scoped BigOperators
open Finset
open SimpleGraph Function


namespace StatMech

namespace Wpb

open StatMech.Lattice

open StatMech.Wad

open StatMech.Wcd

open StatMech.Walls

open StatMech.Euc


theorem wpb_pivot_inj_nonpinch (K : Set (Site 2)) {e e' : Dart}
    (he : IsBoundaryDart K e) (he' : IsBoundaryDart K e')
    (hnp : ¬(wcd_frontCell e ∈ K ∧ wcd_sideCell e ∉ K))
    (hpv : wcd_pivot e = wcd_pivot e') : e = e' := by
  obtain ⟨ht, hh⟩ := he
  obtain ⟨ht', hh'⟩ := he'
  have hhe : e.head = e.tail + e.dir := by rw [Dart.dir_def]; abel
  have hhe' : e'.head = e'.tail + e'.dir := by rw [Dart.dir_def]; abel
  have siteEq : ∀ p q : Site 2, p 0 = q 0 → p 1 = q 1 → p = q := by
    intro p q h0 h1; funext i; fin_cases i; exacts [h0, h1]
  
  have hp0 : (wcd_pivot e).1 = (wcd_pivot e').1 := congrArg Prod.fst hpv
  have hp1 : (wcd_pivot e).2 = (wcd_pivot e').2 := congrArg Prod.snd hpv
  rcases wcd_dir_cases e with hd | hd | hd | hd <;>
    rcases wcd_dir_cases e' with hd' | hd' | hd' | hd' <;>
    simp only [wcd_pivot, wcd_pivotSite, wcd_posPartSite, wcd_siteToVtx_apply, hd, hd',
      Pi.add_apply, Pi.neg_apply, rot90Fun_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, neg_neg, neg_zero, max_self] at hp0 hp1 <;>
  first
    
    | (refine Dart.ext (siteEq _ _ ?_ ?_) (siteEq _ _ ?_ ?_) <;>
        (first
          | omega
          | (simp only [hhe, hhe', hd, hd', Pi.add_apply, Matrix.cons_val_zero,
              Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega)))
    
    | (exfalso; apply hh'
       have heq : e'.head = e.tail := by
         refine siteEq _ _ ?_ ?_ <;>
           (first
             | omega
             | (simp only [hhe, hhe', hd, hd', Pi.add_apply, Matrix.cons_val_zero,
                 Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega))
       rw [heq]; exact ht)
    
    | (exfalso; apply hh
       have heq : e'.tail = e.head := by
         refine siteEq _ _ ?_ ?_ <;>
           (first
             | omega
             | (simp only [hhe, hhe', hd, hd', Pi.add_apply, Matrix.cons_val_zero,
                 Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega))
       rw [← heq]; exact ht')
    
    | (exfalso; apply hnp; refine ⟨?_, ?_⟩
       · have heq : e'.tail = wcd_frontCell e := by
           refine siteEq _ _ ?_ ?_ <;>
             (first
               | omega
               | (simp only [wcd_frontCell, hhe, hhe', hd, hd', Pi.add_apply, Pi.neg_apply,
                   rot90Fun_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
                   Matrix.cons_val_fin_one, neg_neg, neg_zero]; omega))
         rw [← heq]; exact ht'
       · have heq : e'.head = wcd_sideCell e := by
           refine siteEq _ _ ?_ ?_ <;>
             (first
               | omega
               | (simp only [wcd_sideCell, hhe, hhe', hd, hd', Pi.add_apply, Pi.neg_apply,
                   rot90Fun_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
                   Matrix.cons_val_fin_one, neg_neg, neg_zero]; omega))
         rw [← heq]; exact hh')


end Wpb
end StatMech
