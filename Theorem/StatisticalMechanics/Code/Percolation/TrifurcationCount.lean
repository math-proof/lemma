/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMergeGeom
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem tfc_boundary_cross_vertex (n : ℕ) (hn : 1 ≤ n) (z z' : Site d) (hz : z ∈ box d n)
    (hz' : z' ∉ box d n) (hadj : (hypercubicLattice d).Adj z z') :
    z ∈ vertexBoundary d n := by
  rw [mem_box] at hz; rw [mem_box] at hz'; push_neg at hz'
  obtain ⟨i, hi⟩ := hz'
  rw [hypercubicLattice_adj] at hadj
  
  have hipos : 1 ≤ (z i - z' i).natAbs := by
    rcases Nat.eq_zero_or_pos (z i - z' i).natAbs with h0 | hpos
    · exfalso; rw [Int.natAbs_eq_zero, sub_eq_zero] at h0
      have := hz i; rw [h0] at this; omega
    · exact hpos
  
  have hterm : (z i - z' i).natAbs = 1 := by
    by_contra hne
    have hge2 : 2 ≤ (z i - z' i).natAbs := by omega
    have hle : (z i - z' i).natAbs ≤ ∑ j, (z j - z' j).natAbs :=
      Finset.single_le_sum (f := fun j => (z j - z' j).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  
  have hzin : (z i).natAbs = n := by have h1 := hz i; omega
  refine ⟨fun j => hz j, ?_⟩
  rw [mem_box]; push_neg
  exact ⟨i, by rw [hzin]; omega⟩


theorem tfc_walk_crossing {V : Type*} (G : SimpleGraph V) (p : V → Prop) [DecidablePred p] :
    ∀ {x y : V} (w : G.Walk x y), p x → ¬ p y →
      ∃ a b, G.Adj a b ∧ p a ∧ ¬ p b ∧ G.Reachable x a := by
  intro x y w
  induction w with
  | nil => intro hx hy; exact absurd hx hy
  | @cons u v z hadj w' ih =>
    intro hu hz
    by_cases hv : p v
    · obtain ⟨a, b, hab, ha, hb, hr⟩ := ih hv hz
      exact ⟨a, b, hab, ha, hb, (hadj.reachable).trans hr⟩
    · exact ⟨u, v, hadj, hu, hv, Reachable.refl u⟩


theorem tfc_trif_cluster_infinite (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (htri : IsTrifurcation d ω x) : (cluster d ω x).Infinite := by
  obtain ⟨a₁, _, _, _, hconn, hinf, _⟩ := htri
  rw [cluster_eq_of_connected hconn.1]; exact hinf.1


theorem tfc_trif_reaches_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (x : Site d) (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x) :
    ∃ z ∈ vertexBoundary d n, Connected d ω x z := by
  classical
  have hxinf : (cluster d ω x).Infinite := tfc_trif_cluster_infinite ω x htri
  obtain ⟨y, hybox, hyconn⟩ := (cluster_infinite_iff ω x).mp hxinf n
  obtain ⟨w⟩ := hyconn
  obtain ⟨a, b, hab, ha, hb, hr⟩ :=
    tfc_walk_crossing (openSubgraph d ω) (fun v => v ∈ box d n) w hxbox hybox
  have hablat : (hypercubicLattice d).Adj a b := (openSubgraph_le ω) hab
  exact ⟨a, tfc_boundary_cross_vertex n hn a b ha hb hablat, hr⟩


end Percolation
end StatMech
