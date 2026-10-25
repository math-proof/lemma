/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsCycleClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InteriorWindingClose
import Theorem.StatisticalMechanics.Code.Lattice.SegmentDownClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.MatchedConnectivityInterior.Part6
import Theorem.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.KingSegmentDownClose
import Theorem.StatisticalMechanics.Code.Lattice.KingDescentAgnosticClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.KingStepConnectClose
import Theorem.StatisticalMechanics.Code.Lattice.KingNoSeparationClose.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EscapeThickPointClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EscapeWallThickClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.GlobalThickPointClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossArcThickClose.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingPinchClose
import Def.StatisticalMechanics.Code.Lattice.PeierlsCycleClose.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem pcy_crossArcThick_of_crossArcThick {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hcat : cat_CrossArcThick Vc seed) : pcy_CrossArcThick Vc seed :=
  fun _ => hcat


theorem pcy_noKingSeparation_of_fourThin_cycle {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hcyc : Vc.IsCycle) (hseedI : seed ∈ jil_offSupportInterior Vc)
    (hthin : mci_FourThin Vc) (hres : pcy_CrossArcThick Vc seed) :
    ksc_NoKingSeparation Vc seed :=
  cat_noKingSeparation_of_fourThin Vc hseedI hthin (hres hcyc)


theorem pcy_kingRowLinked_of_fourThin_cycle {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hcyc : Vc.IsCycle) (hseedI : seed ∈ jil_offSupportInterior Vc)
    (hthin : mci_FourThin Vc) (hres : pcy_CrossArcThick Vc seed) :
    mci_KingRowLinked Vc seed :=
  cat_kingRowLinked_of_fourThin Vc hseedI hthin (hres hcyc)


theorem pcy_kingInteriorConnected_of_fourThin_cycle {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {z₀ : Site 2} (hcyc : Vc.IsCycle)
    (hz₀ : z₀ ∈ jil_offSupportInterior Vc) (hthin : mci_FourThin Vc)
    (hres : ∀ seed ∈ jil_offSupportInterior Vc, pcy_CrossArcThick Vc seed) :
    mci_KingInteriorConnected Vc :=
  ⟨z₀, hz₀, pcy_kingRowLinked_of_fourThin_cycle Vc hcyc hz₀ hthin (hres z₀ hz₀)⟩


theorem pcy_fig8_crossArcThick : pcy_CrossArcThick wpc_fig8 (![1, 1] : Site 2) :=
  fun hcyc => absurd hcyc pcy_fig8_not_cycle


theorem pcy_fig8_structural_fix :
    ¬ cat_CrossArcThick wpc_fig8 (![1, 1] : Site 2) ∧
    mci_FourThin wpc_fig8 ∧
    ¬ ksc_NoKingSeparation wpc_fig8 (![1, 1] : Site 2) ∧
    ¬ wpc_fig8.IsCycle ∧
    pcy_CrossArcThick wpc_fig8 (![1, 1] : Site 2) :=
  ⟨wpc_cat_crossArcThick_false, wpc_fig8_fourThin, wpc_not_noKingSeparation,
   pcy_fig8_not_cycle, pcy_fig8_crossArcThick⟩


theorem pcy_fjord_on_32 : (![3, 2] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; left
  exact sdc_vsegUp_mem' 3 0 3 2 (by norm_num) (by norm_num)


theorem pcy_fjord_on_30 : (![3, 0] : Site 2) ∈ sdc_fjord.support := by
  unfold sdc_fjord
  simp only [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse]
  right; left
  exact sdc_vsegUp_mem' 3 0 3 0 (by norm_num) (by norm_num)


theorem pcy_fjord_throat_three_neighbors :
    (![3, 1] : Site 2) ∈ sdc_fjord.support ∧
    (hypercubicLattice 2).Adj (![3, 1] : Site 2) (![3, 0] : Site 2) ∧
    (hypercubicLattice 2).Adj (![3, 1] : Site 2) (![3, 2] : Site 2) ∧
    (hypercubicLattice 2).Adj (![3, 1] : Site 2) (![4, 1] : Site 2) ∧
    (![3, 0] : Site 2) ∈ sdc_fjord.support ∧ (![3, 2] : Site 2) ∈ sdc_fjord.support ∧
    (![4, 1] : Site 2) ∈ sdc_fjord.support ∧
    (![3, 0] : Site 2) ≠ (![3, 2] : Site 2) ∧ (![3, 0] : Site 2) ≠ (![4, 1] : Site 2) ∧
    (![3, 2] : Site 2) ≠ (![4, 1] : Site 2) :=
  ⟨mci_fjord_on_31,
   (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide),
   (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide),
   (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide),
   pcy_fjord_on_30, pcy_fjord_on_32, sdc_fjord_on_41,
   (by intro h; have := congrFun h 1; simp at this),
   (by intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega),
   (by intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega)⟩


theorem pcy_fjord_three_support_neighbors (hcyc : sdc_fjord.IsCycle) :
    kns_ThickPoint sdc_fjord :=
  pcy_thickPoint_of_three_support_neighbors sdc_fjord hcyc
    (u := (![3, 1] : Site 2)) (v₁ := (![3, 0] : Site 2)) (v₂ := (![3, 2] : Site 2))
    (v₃ := (![4, 1] : Site 2))
    mci_fjord_on_31
    (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
    (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
    (by rw [hypercubicLattice_adj, Fin.sum_univ_two]; decide)
    pcy_fjord_on_30 pcy_fjord_on_32 sdc_fjord_on_41
    (by intro h; have := congrFun h 1; simp at this)
    (by intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega)
    (by intro h; have := congrFun h 0; simp only [Matrix.cons_val_zero] at this; omega)


theorem pcy_ksd_crossArcThick : pcy_CrossArcThick ksd_stair (![1, 1] : Site 2) :=
  pcy_crossArcThick_of_crossArcThick ksd_stair cat_ksd_crossArcThick


theorem pcy_kda_crossArcThick : pcy_CrossArcThick kda_stairDR (![3, 1] : Site 2) :=
  pcy_crossArcThick_of_crossArcThick kda_stairDR cat_kda_crossArcThick


theorem pcy_fjord_crossArcThick : pcy_CrossArcThick sdc_fjord (![5, 1] : Site 2) :=
  pcy_crossArcThick_of_crossArcThick sdc_fjord cat_fjord_crossArcThick


theorem pcy_kingRowLinked_summary {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {seed : Site 2} (hcyc : Vc.IsCycle) (hseedI : seed ∈ jil_offSupportInterior Vc)
    (hthin : mci_FourThin Vc) :
    pcy_CrossArcThick Vc seed → mci_KingRowLinked Vc seed :=
  pcy_kingRowLinked_of_fourThin_cycle Vc hcyc hseedI hthin

end Lattice
end StatMech
