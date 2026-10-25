/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
import Def.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box


@[simp] theorem jec_mem_belowSet (y : ℤ) (p : Site 2) :
    p ∈ jec_belowSet y ↔ p 1 ≤ y - 1 := Iff.rfl


theorem jec_belowSet_bdEdge (y : ℤ) (u v : Site 2) (hadj : (hypercubicLattice 2).Adj u v) :
    bdEdge (jec_belowSet y) s(u, v) ↔
      (u 0 = v 0) ∧ ((u 1 = y - 1 ∧ v 1 = y) ∨ (v 1 = y - 1 ∧ u 1 = y)) := by
  rw [bdEdge_mk]; simp only [jec_mem_belowSet]
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  omega


theorem jec_ray_eq_below (z : Site 2) {x y : Site 2} (w : (hypercubicLattice 2).Walk x y)
    (hfar : ∀ p ∈ w.support, p 0 ≤ z 0 - 1) :
    jec_rayCount z w = crossCount (jec_belowSet (z 1)) w := by
  classical
  rw [jec_rayCount, crossCount]
  refine List.countP_congr ?_
  intro e he
  obtain ⟨u, v⟩ := e
  have hadj : (hypercubicLattice 2).Adj u v := w.adj_of_mem_edges he
  have hcu := hfar u (w.fst_mem_support_of_mem_edges he)
  have hcv := hfar v (w.snd_mem_support_of_mem_edges he)
  simp only [decide_eq_true_eq]
  show jec_rayEdge z s(u, v) ↔ bdEdge (jec_belowSet (z 1)) s(u, v)
  rw [jec_rayEdge_mk, jec_belowSet_bdEdge (z 1) u v hadj]
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩


theorem jec_ray_even_far {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2)
    (hfar : ∀ p ∈ Vc.support, p 0 ≤ z 0 - 1) :
    Even (jec_rayCount z Vc) := by
  rw [jec_ray_eq_below z Vc hfar]
  exact crossCount_even_of_loop (jec_belowSet (z 1)) Vc


theorem jec_rayCount_eq_zero_of_right (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (h : ∀ p ∈ w.support, z 0 ≤ p 0) :
    jec_rayCount z w = 0 := by
  classical
  rw [jec_rayCount, List.countP_eq_zero]
  intro e he
  obtain ⟨u, v⟩ := e
  have hu := h u (w.fst_mem_support_of_mem_edges he)
  simp only [decide_eq_true_eq]
  show ¬ jec_rayEdge z s(u, v)
  rw [jec_rayEdge_mk]
  omega


theorem jec_arcSeparatingSet (α β c d a0 b0 : ℤ)
    (hαβ : α < β) (hcd : c ≤ d)
    (ha0 : α ≤ a0) (ha0' : a0 ≤ β) (hb0 : α ≤ b0) (hb0' : b0 ≤ β)
    (V : (hypercubicLattice 2).Walk ![a0, c] ![b0, d])
    (hVbox : ∀ p ∈ V.support, p ∈ rect α β c d)
    (P : Set (Site 2)) (hVP : ∀ p ∈ V.support, p ∈ P) :
    ArcSeparatingSet P α β c d := by
  classical
  
  set R := jec_retPath α a0 b0 c d ha0 hb0 hcd with hR
  set Vc : (hypercubicLattice 2).Walk ![a0, c] ![a0, c] := V.append R with hVc
  
  have ha_mem : (![a0, c] : Site 2) ∈ V.support := V.start_mem_support
  have hb_mem : (![b0, d] : Site 2) ∈ V.support := V.end_mem_support
  
  have hVcol : ∀ p ∈ V.support, α ≤ p 0 ∧ p 0 ≤ β ∧ c ≤ p 1 ∧ p 1 ≤ d := by
    intro p hp; exact hVbox p hp
  
  have hVccol : ∀ p ∈ Vc.support, p 0 ≤ β := by
    intro p hp
    rw [hVc, SimpleGraph.Walk.mem_support_append_iff] at hp
    rcases hp with h | h
    · exact (hVcol p h).2.1
    · exact (jec_retPath_col α β a0 b0 c d ha0 hb0 hcd ha0' hb0' (le_of_lt hαβ) h).2
  
  have hRbox : ∀ p ∈ R.support, p ∈ rect α β c d → p ∈ V.support := by
    intro p hpR hpbox
    rw [mem_rect] at hpbox
    rcases jec_retPath_support α a0 b0 c d ha0 hb0 hcd hpR with h | h | h | h | h
    · omega 
    · omega 
    · omega 
    · rw [h]; exact hb_mem  
    · rw [h]; exact ha_mem  
  
  have hVcbox : ∀ p ∈ Vc.support, p ∈ rect α β c d → p ∈ V.support := by
    intro p hp hpbox
    rw [hVc, SimpleGraph.Walk.mem_support_append_iff] at hp
    rcases hp with h | h
    · exact h
    · exact hRbox p h hpbox
  
  refine ⟨jec_leftRegion Vc \ {z | z 0 = β ∧ z ∈ V.support}, ?_, ?_, ?_⟩
  · 
    intro z hzbox hzα
    rw [mem_rect] at hzbox
    refine ⟨?_, ?_⟩
    · 
      rw [jec_mem_leftRegion, hVc, jec_rayCount_append]
      have hV0 : jec_rayCount z V = 0 := by
        refine jec_rayCount_eq_zero_of_right z V ?_
        intro p hp; rw [hzα]; exact (hVcol p hp).1
      have hRray : jec_rayCount z R = 1 := by
        rw [hR, jec_rayCount_retPath]
        rw [if_neg (by rw [hzα]; omega), if_pos ?_, if_neg (by rw [hzα]; omega)]
        rw [hzα]
        refine ⟨by omega, by omega, ?_⟩
        rw [show ((d+1-(c-1)).toNat : ℤ) = d+1-(c-1) by omega]; omega
      rw [hV0, hRray]; decide
    · 
      simp only [Set.mem_setOf_eq, not_and]
      intro hzβ; omega
  · 
    intro z hzbox hzβ
    rw [mem_rect] at hzbox
    rw [Set.mem_diff]
    rintro ⟨hzleft, hzrem⟩
    
    by_cases hzV : z ∈ V.support
    · 
      exact hzrem ⟨hzβ, hzV⟩
    · 
      have hzVc : z ∉ Vc.support := by
        rw [hVc, SimpleGraph.Walk.mem_support_append_iff]
        rintro (h | h)
        · exact hzV h
        · exact hzV (hRbox z h (by rw [mem_rect]; exact hzbox))
      
      have hz'0 : (![z 0 + 1, z 1] : Site 2) 0 = z 0 + 1 := by simp
      have hz'1 : (![z 0 + 1, z 1] : Site 2) 1 = z 1 := by simp
      have hray_eq : jec_rayCount (![z 0 + 1, z 1] : Site 2) Vc = jec_rayCount z Vc :=
        jec_rayCount_horizontalStep z (![z 0 + 1, z 1]) hz'0 hz'1 Vc hzVc
      have hfar : ∀ p ∈ Vc.support, p 0 ≤ (![z 0 + 1, z 1] : Site 2) 0 - 1 := by
        intro p hp; have := hVccol p hp; rw [hz'0, hzβ]; omega
      have heven : Even (jec_rayCount z Vc) := by
        rw [← hray_eq]; exact jec_ray_even_far Vc (![z 0 + 1, z 1]) hfar
      rw [jec_mem_leftRegion] at hzleft
      exact hzleft heven
  · 
    intro u v hubox hvbox hadj hbd
    
    rw [bdEdge_mk] at hbd
    
    have key : ∀ x' y' : Site 2, x' ∈ rect α β c d → y' ∈ rect α β c d →
        (hypercubicLattice 2).Adj x' y' →
        x' ∈ jec_leftRegion Vc \ {z | z 0 = β ∧ z ∈ V.support} →
        y' ∉ jec_leftRegion Vc \ {z | z 0 = β ∧ z ∈ V.support} →
        x' ∈ V.support ∨ y' ∈ V.support := by
      intro x' y' hx'box hy'box hadj' hx'S hy'S
      rw [Set.mem_diff] at hx'S
      obtain ⟨hx'left, _hx'rem⟩ := hx'S
      rw [Set.mem_diff, not_and_or, not_not] at hy'S
      rcases hy'S with hy'left | hy'rem
      · 
        have hbdL : bdEdge (jec_leftRegion Vc) s(x', y') := by
          rw [bdEdge_mk]; exact ⟨fun _ => hy'left, fun _ => hx'left⟩
        rcases jec_leftRegion_bdEdge_support Vc hadj' hbdL with hsupp | hsupp
        · exact Or.inl (hVcbox x' hsupp hx'box)
        · exact Or.inr (hVcbox y' hsupp hy'box)
      · 
        exact Or.inr hy'rem.2
    
    by_cases huS : u ∈ jec_leftRegion Vc \ {z | z 0 = β ∧ z ∈ V.support}
    · have hvS : v ∉ jec_leftRegion Vc \ {z | z 0 = β ∧ z ∈ V.support} := hbd.mp huS
      rcases key u v hubox hvbox hadj huS hvS with h | h
      · exact Or.inl (hVP u h)
      · exact Or.inr (hVP v h)
    · 
      have hvS : v ∈ jec_leftRegion Vc \ {z | z 0 = β ∧ z ∈ V.support} := by
        by_contra hvS
        exact huS (hbd.mpr hvS)
      rcases key v u hvbox hubox hadj.symm hvS huS with h | h
      · exact Or.inr (hVP v h)
      · exact Or.inl (hVP u h)


open StatMech.Universality in


theorem jec_vsFix_arc_sides (ω : ConfigSpace (Sym2 (Site 2))) {α β m m' c d : ℤ}
    (hαβ : α < β) (hcd : c ≤ d) :
    StatMech.Universality.vsFix_arc_sides ω α β m m' c d := by
  intro hαm hmm' hm'β xB hxB hxBbot yT hyT hcV
  
  obtain ⟨V, hVsupp⟩ := tpc_arcWalk_support hxB (topSide_subset hyT) hcV
  
  have hxB1 : xB 1 = c := hxBbot.2
  have hyT1 : yT 1 = d := hyT.2
  have hxBrect : xB ∈ rect m m' c d := hxB
  have hyTrect : yT ∈ rect m m' c d := topSide_subset hyT
  
  have hxBeq : xB = ![xB 0, c] := by ext i; fin_cases i <;> simp [hxB1]
  have hyTeq : yT = ![yT 0, d] := by ext i; fin_cases i <;> simp [hyT1]
  set V' : (hypercubicLattice 2).Walk ![xB 0, c] ![yT 0, d] := V.copy hxBeq hyTeq with hV'
  
  have hV'supp : ∀ p ∈ V'.support, p ∈ overlapComp ω m m' c d xB hxB := by
    intro p hp; rw [hV', SimpleGraph.Walk.support_copy] at hp; exact hVsupp p hp
  have hV'box : ∀ p ∈ V'.support, p ∈ rect α β c d := by
    intro p hp
    have hpO : p ∈ rect m m' c d := (hV'supp p hp).1
    rw [mem_rect] at hpO ⊢; omega
  
  have ha0 : α ≤ xB 0 := by rw [mem_rect] at hxBrect; omega
  have ha0' : xB 0 ≤ β := by rw [mem_rect] at hxBrect; omega
  have hb0 : α ≤ yT 0 := by rw [mem_rect] at hyTrect; omega
  have hb0' : yT 0 ≤ β := by rw [mem_rect] at hyTrect; omega
  
  exact jec_arcSeparatingSet α β c d (xB 0) (yT 0) hαβ hcd ha0 ha0' hb0 hb0'
    V' hV'box (overlapComp ω m m' c d xB hxB) hV'supp


theorem jec_rsw_strip_glue
    (μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site 2))))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hpa : StatMech.Universality.PositivelyAssociated μ) {a m m' b c d : ℤ}
    (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hamL : a < m') (hmbR : m < b) (hcd : c ≤ d) :
    μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
      ≤ μ.real (horizontalCrossingEvent a b c d) :=
  StatMech.Universality.vsFix_rsw_strip_glue_of_arc_sides μ hpa ham hmm' hm'b
    (fun ω => jec_vsFix_arc_sides ω hamL hcd)
    (fun ω => jec_vsFix_arc_sides ω hmbR hcd)

end Lattice
end StatMech
