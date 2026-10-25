/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/benentryleg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.brpreproute.Part2
import Theorem.StatisticalMechanics.Code.Walls.bararmray
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Def.StatisticalMechanics.Code.Walls.benentryleg
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem ben_entry_of_clusterReconnect (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (tipj x b : Site d)
    (hxb : (openSubgraph d ω).Reachable x b)
    (hxesc : (cluster d (removeSites (bc61_boxAround d L tipj) ω) x).Infinite)
    (hbesc : (cluster d (removeSites (bc61_boxAround d L tipj) ω) b).Infinite)
    (hrec : ben_ClusterReconnect ω L tipj) :
    (bc67_contractedLattice ω L tipj).Reachable x b :=
  hrec x b hxb hxesc hbesc


theorem ben_full_reconnect_of_escapes (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (hd : 2 ≤ d)
    (tipj x b : Site d)
    (hxesc : (cluster d (removeSites (bc61_boxAround d L tipj) ω) x).Infinite)
    (hbesc : (cluster d (removeSites (bc61_boxAround d L tipj) ω) b).Infinite) :
    ∃ (hx : x ∉ (↑(bc61_boxAround d L tipj) : Set (Site d)))
      (hb : b ∉ (↑(bc61_boxAround d L tipj) : Set (Site d))),
      ((hypercubicLattice d).induce (↑(bc61_boxAround d L tipj) : Set (Site d))ᶜ).Reachable
        ⟨x, hx⟩ ⟨b, hb⟩ := by
  obtain ⟨r, hr0, hrinj, _, hrlat, hravoid⟩ := ben_escape_of_notEnclosed ω L tipj x hxesc
  obtain ⟨s, hs0, hsinj, _, hslat, hsavoid⟩ := ben_escape_of_notEnclosed ω L tipj b hbesc
  have hravoid' : ∀ k, r k ∉ (↑(bc61_boxAround d L tipj) : Set (Site d)) := by
    intro k; rw [Finset.mem_coe]; exact hravoid k
  have hsavoid' : ∀ k, s k ∉ (↑(bc61_boxAround d L tipj) : Set (Site d)) := by
    intro k; rw [Finset.mem_coe]; exact hsavoid k
  have hx : x ∉ (↑(bc61_boxAround d L tipj) : Set (Site d)) := hr0 ▸ hravoid' 0
  have hb : b ∉ (↑(bc61_boxAround d L tipj) : Set (Site d)) := hs0 ▸ hsavoid' 0
  refine ⟨hx, hb, ?_⟩
  have hreach := ben_escapes_same_fullComponent (bc61_boxAround d L tipj) hd r s hrinj hsinj
    hrlat hslat hravoid' hsavoid'
  
  have hbase_r : (⟨r 0, hravoid' 0⟩ : ↥(↑(bc61_boxAround d L tipj) : Set (Site d))ᶜ)
      = ⟨x, hx⟩ := by subst hr0; rfl
  have hbase_s : (⟨s 0, hsavoid' 0⟩ : ↥(↑(bc61_boxAround d L tipj) : Set (Site d))ᶜ)
      = ⟨b, hb⟩ := by subst hs0; rfl
  rw [hbase_r, hbase_s] at hreach
  exact hreach


theorem ben_entry_clause_of_residue (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x : Site d)
    (tip b : Fin 3 → Site d)
    (hrec : ∀ j, ben_ClusterReconnect ω L (tip j))
    (hxb : ∀ i, (openSubgraph d ω).Reachable x (b i))
    (hxesc : ∀ i j, i ≠ j →
      (cluster d (removeSites (bc61_boxAround d L (tip j)) ω) x).Infinite)
    (hbesc : ∀ i j, i ≠ j →
      (cluster d (removeSites (bc61_boxAround d L (tip j)) ω) (b i)).Infinite) :
    ∀ i j, i ≠ j → (bc67_contractedLattice ω L (tip j)).Reachable x (b i) := by
  intro i j hij
  exact ben_entry_of_clusterReconnect ω L (tip j) x (b i)
    (hxb i) (hxesc i j hij) (hbesc i j hij) (hrec j)


theorem ben_repRoute_of_residue (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x : Site d)
    (tip b : Fin 3 → Site d)
    (hrec : ∀ j, ben_ClusterReconnect ω L (tip j))
    (hxb : ∀ i, (openSubgraph d ω).Reachable x (b i))
    (hxesc : ∀ i j, i ≠ j →
      (cluster d (removeSites (bc61_boxAround d L (tip j)) ω) x).Infinite)
    (hbesc : ∀ i j, i ≠ j →
      (cluster d (removeSites (bc61_boxAround d L (tip j)) ω) (b i)).Infinite)
    (htail : ∀ i j, i ≠ j → (bc67_contractedLattice ω L (tip j)).Reachable (b i) (tip i)) :
    bcr_RepRoute ω L x tip :=
  brp_repRoute_of_entry ω L x tip b
    (ben_entry_clause_of_residue ω L x tip b hrec hxb hxesc hbesc) htail


theorem ben_bk_of_trifData (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bgc_TrifForestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bar_bk_uniqueness_of_trifData p hp1 hp0 hdata


theorem ben_residue_is_openLift (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (hd : 2 ≤ d)
    (tipj : Site d) :
    ben_ClusterReconnect ω L tipj ↔
      (∀ u v : Site d, (openSubgraph d ω).Reachable u v →
        (cluster d (removeSites (bc61_boxAround d L tipj) ω) u).Infinite →
        (cluster d (removeSites (bc61_boxAround d L tipj) ω) v).Infinite →
        
        (∃ (hu : u ∉ (↑(bc61_boxAround d L tipj) : Set (Site d)))
           (hv : v ∉ (↑(bc61_boxAround d L tipj) : Set (Site d))),
          ((hypercubicLattice d).induce (↑(bc61_boxAround d L tipj) : Set (Site d))ᶜ).Reachable
            ⟨u, hu⟩ ⟨v, hv⟩) →
        
        (bc67_contractedLattice ω L tipj).Reachable u v) := by
  constructor
  · intro hrec u v huv hu hv _; exact hrec u v huv hu hv
  · intro h u v huv hu hv
    exact h u v huv hu hv (ben_full_reconnect_of_escapes ω L hd tipj u v hu hv)


theorem ben_axis_out_x (L : ℕ) (c : ℤ) (h : L < c.natAbs) :
    bc57_pt c 0 ∉ (↑(bc61_boxAround 2 L (bc57_pt 0 0)) : Set (Site 2)) := by
  rw [Finset.mem_coe]; exact bcr_out (Or.inl h)


theorem ben_axis_out_y (L : ℕ) (c : ℤ) (h : L < c.natAbs) :
    bc57_pt 0 c ∉ (↑(bc61_boxAround 2 L (bc57_pt 0 0)) : Set (Site 2)) := by
  rw [Finset.mem_coe]; exact bcr_out (Or.inr h)


theorem ben_natAbs_far (L k : ℕ) : L < ((L : ℤ) + 1 + (k : ℤ)).natAbs := by
  rw [show ((L : ℤ) + 1 + (k : ℤ)) = ((L + 1 + k : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]
  omega


theorem ben_freeReconnect_witness (L : ℕ) :
    ((hypercubicLattice 2).induce (↑(bc61_boxAround 2 L (bc57_pt 0 0)) : Set (Site 2))ᶜ).Reachable
      ⟨bc57_pt ((L : ℤ) + 1) 0, ben_axis_out_x L ((L : ℤ) + 1) (by
        rw [show ((L : ℤ) + 1) = ((L + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]; omega)⟩
      ⟨bc57_pt 0 ((L : ℤ) + 1), ben_axis_out_y L ((L : ℤ) + 1) (by
        rw [show ((L : ℤ) + 1) = ((L + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]; omega)⟩ := by
  classical
  set r : ℕ → Site 2 := fun k => bc57_pt ((L : ℤ) + 1 + (k : ℤ)) 0 with hr
  set s : ℕ → Site 2 := fun k => bc57_pt 0 ((L : ℤ) + 1 + (k : ℤ)) with hs
  have hrinj : Function.Injective r := by
    intro a c hac
    have := congrArg (fun p => p 0) hac
    simp only [hr, bc57_pt_fst] at this
    have : (a : ℤ) = (c : ℤ) := by omega
    exact_mod_cast this
  have hsinj : Function.Injective s := by
    intro a c hac
    have := congrArg (fun p => p 1) hac
    simp only [hs, bc57_pt_snd] at this
    have : (a : ℤ) = (c : ℤ) := by omega
    exact_mod_cast this
  have hrlat : ∀ k, (hypercubicLattice 2).Adj (r k) (r (k + 1)) := by
    intro k
    have h := bc57_pt_adj ((L : ℤ) + 1 + (k : ℤ)) 0
    rwa [show (L : ℤ) + 1 + (k : ℤ) + 1 = (L : ℤ) + 1 + ((k + 1 : ℕ) : ℤ) by push_cast; ring] at h
  have hslat : ∀ k, (hypercubicLattice 2).Adj (s k) (s (k + 1)) := by
    intro k
    have h := bcr_vert_adj ((L : ℤ) + 1 + (k : ℤ))
    rwa [show (L : ℤ) + 1 + (k : ℤ) + 1 = (L : ℤ) + 1 + ((k + 1 : ℕ) : ℤ) by push_cast; ring] at h
  have hravoid : ∀ k, r k ∉ (↑(bc61_boxAround 2 L (bc57_pt 0 0)) : Set (Site 2)) := by
    intro k; exact ben_axis_out_x L _ (ben_natAbs_far L k)
  have hsavoid : ∀ k, s k ∉ (↑(bc61_boxAround 2 L (bc57_pt 0 0)) : Set (Site 2)) := by
    intro k; exact ben_axis_out_y L _ (ben_natAbs_far L k)
  have hreach := ben_escapes_same_fullComponent (bc61_boxAround 2 L (bc57_pt 0 0)) (by norm_num)
    r s hrinj hsinj hrlat hslat hravoid hsavoid
  
  have hr0 : r 0 = bc57_pt ((L : ℤ) + 1) 0 := by simp [hr]
  have hs0 : s 0 = bc57_pt 0 ((L : ℤ) + 1) := by simp [hs]
  have e1 : (⟨r 0, hravoid 0⟩ : ↥(↑(bc61_boxAround 2 L (bc57_pt 0 0)) : Set (Site 2))ᶜ)
      = ⟨bc57_pt ((L : ℤ) + 1) 0, ben_axis_out_x L ((L : ℤ) + 1) (by
          rw [show ((L : ℤ) + 1) = ((L + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]; omega)⟩ :=
    Subtype.ext hr0
  have e2 : (⟨s 0, hsavoid 0⟩ : ↥(↑(bc61_boxAround 2 L (bc57_pt 0 0)) : Set (Site 2))ᶜ)
      = ⟨bc57_pt 0 ((L : ℤ) + 1), ben_axis_out_y L ((L : ℤ) + 1) (by
          rw [show ((L : ℤ) + 1) = ((L + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]; omega)⟩ :=
    Subtype.ext hs0
  rw [e1, e2] at hreach
  exact hreach


theorem ben_entry_conclusion_satisfiable (L R : ℕ) (hR : L < R) :
    bcr_RepRoute bcr_cross L (bc57_pt 0 0) (brp_witArm R) :=
  brp_cross_repRoute L R hR


theorem ben_status :
    
    (∀ {V : Type} [inst : DecidableEq V] {G : SimpleGraph V} [inst2 : LocallyFinite G] {v : V},
      (ray34_AvoidCluster G ∅ v).Infinite → ∀ (T : Finset V),
      ∃ b, ray34_AvoidReach G ∅ v b ∧ (ray34_AvoidCluster G (↑T) b).Infinite) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ), 2 ≤ d → ∀ (tipj x b : Site d),
      (cluster d (removeSites (bc61_boxAround d L tipj) ω) x).Infinite →
      (cluster d (removeSites (bc61_boxAround d L tipj) ω) b).Infinite →
      ∃ (hx : x ∉ (↑(bc61_boxAround d L tipj) : Set (Site d)))
        (hb : b ∉ (↑(bc61_boxAround d L tipj) : Set (Site d))),
        ((hypercubicLattice d).induce (↑(bc61_boxAround d L tipj) : Set (Site d))ᶜ).Reachable
          ⟨x, hx⟩ ⟨b, hb⟩) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (tipj x b : Site d),
      (openSubgraph d ω).Reachable x b →
      (cluster d (removeSites (bc61_boxAround d L tipj) ω) x).Infinite →
      (cluster d (removeSites (bc61_boxAround d L tipj) ω) b).Infinite →
      ben_ClusterReconnect ω L tipj →
      (bc67_contractedLattice ω L tipj).Reachable x b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro V _ G _ v hinf T; exact ben_ray34_gap hinf T
  · intro ω L hd tipj x b hxesc hbesc; exact ben_full_reconnect_of_escapes ω L hd tipj x b hxesc hbesc
  · intro ω L tipj x b hxb hxesc hbesc hrec
    exact ben_entry_of_clusterReconnect ω L tipj x b hxb hxesc hbesc hrec

end StatMech.Walls
