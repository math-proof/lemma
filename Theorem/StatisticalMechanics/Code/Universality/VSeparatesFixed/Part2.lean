/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/VSeparatesFixed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.Strip.Part2
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.RSWStrip.Part3
import Theorem.StatisticalMechanics.Code.Universality.HVIntersection.Part2
import Theorem.StatisticalMechanics.Code.Universality.VSeparates.Part2
import Def.StatisticalMechanics.Code.Universality.VSeparatesFixed.Part2
open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip


theorem vsFix_arc_sides_imp (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (harc : vsFix_arc_sides ω α β m m' c d) :
    vsFix_VSeparatesHFixed ω α β m m' c d := by
  classical
  intro hαm hmm' hm'β xB hxB hxBbot yT hyT hcV x y hx0 hy0 wH
  
  obtain ⟨L, hLleft, hLright, hLedge⟩ := harc hαm hmm' hm'β xB hxB hxBbot yT hyT hcV
  
  set wL : (hypercubicLattice 2).Walk (x : Site 2) (y : Site 2) :=
    liftWalk ω (rect α β c d) wH with hwL
  
  have hxL : (x : Site 2) ∈ L := hLleft (x : Site 2) x.2 hx0
  have hyL : (y : Site 2) ∉ L := hLright (y : Site 2) y.2 hy0
  
  have hodd : ¬ Even (crossCount L wL) := by
    rw [crossCount_parity]
    intro h
    exact hyL (h.mp hxL)
  
  have hbd : ∃ e ∈ wL.edges, bdEdge L e := by
    by_contra hcon
    apply hodd
    have hz : crossCount L wL = 0 := by
      rw [crossCount, List.countP_eq_zero]
      intro e he
      simp only [decide_eq_true_eq]
      exact fun hb => hcon ⟨e, he, hb⟩
    rw [hz]; exact ⟨0, rfl⟩
  obtain ⟨e, hemem, hebd⟩ := hbd
  
  
  induction e with
  | h u v =>
    
    
    have hu_supp : u ∈ wL.support := wL.fst_mem_support_of_mem_edges hemem
    have hv_supp : v ∈ wL.support := wL.snd_mem_support_of_mem_edges hemem
    obtain ⟨u', hu'_mem, hu'_eq⟩ := liftWalk_support_mem ω (rect α β c d) wH hu_supp
    obtain ⟨v', hv'_mem, hv'_eq⟩ := liftWalk_support_mem ω (rect α β c d) wH hv_supp
    have hu_box : u ∈ rect α β c d := hu'_eq ▸ u'.2
    have hv_box : v ∈ rect α β c d := hv'_eq ▸ v'.2
    
    have huv_adj : (hypercubicLattice 2).Adj u v := wL.adj_of_mem_edges hemem
    
    rcases hLedge u v hu_box hv_box huv_adj hebd with hUcomp | hVcomp
    · 
      exact ⟨u', hu'_mem, hu'_eq ▸ hUcomp⟩
    · 
      exact ⟨v', hv'_mem, hv'_eq ▸ hVcomp⟩


theorem vsFix_rsw_strip_glue_of_arc_sides (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {a m m' b c d : ℤ} (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (harcL : ∀ ω, vsFix_arc_sides ω a m' m m' c d)
    (harcR : ∀ ω, vsFix_arc_sides ω m b m m' c d) :
    μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
      ≤ μ.real (horizontalCrossingEvent a b c d) :=
  vsFix_rsw_strip_glue μ hpa ham hmm' hm'b
    (fun ω => vsFix_arc_sides_imp ω a m' m m' c d (harcL ω))
    (fun ω => vsFix_arc_sides_imp ω m b m m' c d (harcR ω))

end Universality
end StatMech
