/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SecondPeelingClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SpanForestArmsClose.Part2
import Def.StatisticalMechanics.Code.Percolation.ArmReachComponentClose
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem arc_neighbour_in_box_succ {x c : Site d} {n : ℕ} (hx : x ∈ box d n)
    (hadj : (hypercubicLattice d).Adj x c) : c ∈ box d (n + 1) := by
  rw [hypercubicLattice_adj] at hadj
  rw [mem_box] at hx ⊢
  intro i
  
  have hcoord : (x i - c i).natAbs ≤ 1 := by
    have hle : (x i - c i).natAbs ≤ ∑ j, (x j - c j).natAbs :=
      Finset.single_le_sum (f := fun j => (x j - c j).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have := hx i
  omega


theorem arc_trif_arm_data (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hres : arc_TrifArmsRemoveSiteInfinite ω n)
    (x : Site d) (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x) :
    ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d),
      (∀ i, (openSubgraph d ω).Adj x (c i)) ∧
      (∀ i, c i ≠ x) ∧
      (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
       ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
       ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧
      (∀ i, zr i ∈ vertexBoundary d (n + 1) ∧
        ∃ w : (openSubgraph d (removeSite x ω)).Walk (c i) (zr i), x ∉ w.support) := by
  classical
  obtain ⟨c, hadj, hne, hcut, hinf⟩ := hres x hxbox htri
  
  have hcbox : ∀ i, c i ∈ box d (n + 1) := fun i =>
    arc_neighbour_in_box_succ hxbox (hadj i).1
  
  choose zr hzrb hzrw using fun i =>
    arc_infinite_cluster_reaches_boundary ω (n + 1) (by omega) x (c i) (hne i) (hcbox i) (hinf i)
  exact ⟨c, zr, hadj, hne, hcut, fun i => ⟨hzrb i, hzrw i⟩⟩


theorem arc_armForestReaching_of_residue_single_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (_hxbox : x ∈ box d n) (_htri : IsTrifurcation d ω x)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
    (c : Fin 3 → Site d)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (c i))
    (hne : ∀ i, c i ≠ x)
    (hcut : ¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
            ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
            ¬ Connected d (removeSite x ω) (c 1) (c 2))
    (hbdry : ∀ i, c i ∈ vertexBoundary d n)
    (hinj : Function.Injective c) :
    sfa_ArmForestReaching ω n :=
  sfa_armForestReaching_star ω n c hsingle hadj hbdry hne hinj hcut


theorem arc_Tcount_le_boundary_of_residue_single_boundary (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) {x : Site d} (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
    (c : Fin 3 → Site d)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (c i))
    (hne : ∀ i, c i ≠ x)
    (hcut : ¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
            ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
            ¬ Connected d (removeSite x ω) (c 1) (c 2))
    (hbdry : ∀ i, c i ∈ vertexBoundary d n)
    (hinj : Function.Injective c) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  sfa_Tcount_le_boundary_of_armForestReaching ω n
    (arc_armForestReaching_of_residue_single_boundary ω n hxbox htri hsingle c hadj hne hcut
      hbdry hinj)


end Percolation
end StatMech
