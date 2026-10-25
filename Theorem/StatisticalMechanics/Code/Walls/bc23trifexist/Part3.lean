/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc23trifexist.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc12core.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc21trifurc.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc19menger.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc20mengerroute.Part5
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
import Theorem.StatisticalMechanics.Code.Percolation.MengerRouting.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BoxMengerAttachment.Part3
import Def.StatisticalMechanics.Code.Walls.bc23trifexist.Part2
open Set SimpleGraph MeasureTheory
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech.Walls

variable {d : ℕ}


theorem bc23_mengerRoutingCover_of_latticeCorridorRouting (d n : ℕ)
    (h : bc23_LatticeCorridorRouting d n) : MengerRoutingCover d n := by
  intro ω hω
  obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, w₁, w₂, w₃, hne, hadj, hw0, h0, hinf,
    S₁, S₂, S₃, hb, hcl₁, hcl₂, hcl₃, hd⟩ := h ω hω
  exact bc23_mengerCore_of_latticeCorridors ω a₁ a₂ a₃ b₁ b₂ b₃ w₁ w₂ w₃ hne hadj
    hw0.1 hw0.2.1 hw0.2.2 h0 hinf S₁ S₂ S₃ hb.1 hb.2.1 hb.2.2 hcl₁ hcl₂ hcl₃
    hd.1 hd.2.1 hd.2.2


theorem bc23_burtonKeane_uniqueness_of_latticeCorridorRouting
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hr : ∀ n : ℕ, bc23_LatticeCorridorRouting d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  mng_burton_keane_uniqueness_mengerCover μ herg hfe bdry hbound hvol hdens
    (fun n => bc23_mengerRoutingCover_of_latticeCorridorRouting d n (hr n))


theorem bc23_nil_support (a : Site d) : ((Walk.nil : (hypercubicLattice d).Walk a a)).support = [a] := by
  simp


theorem bc23_mengerCore_of_originFree (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (h0 : (0 : Site d) ∉ cluster d ω a₁ ∧ (0 : Site d) ∉ cluster d ω a₂ ∧
      (0 : Site d) ∉ cluster d ω a₃)
    (hinf : (cluster d ω a₁).Infinite ∧ (cluster d ω a₂).Infinite ∧ (cluster d ω a₃).Infinite)
    (hdist : cluster d ω a₁ ≠ cluster d ω a₂ ∧ cluster d ω a₁ ≠ cluster d ω a₃ ∧
      cluster d ω a₂ ≠ cluster d ω a₃) :
    MengerCore ω := by
  classical
  
  have hw0 : ∀ a : Site d, a ≠ 0 → (0 : Site d) ∉ ((Walk.nil : (hypercubicLattice d).Walk a a)).support := by
    intro a ha hmem; rw [bc23_nil_support] at hmem; simp only [List.mem_singleton] at hmem
    exact ha hmem.symm
  have ha0₁ : a₁ ≠ 0 := ((hypercubicLattice d).ne_of_adj hadj.1).symm
  have ha0₂ : a₂ ≠ 0 := ((hypercubicLattice d).ne_of_adj hadj.2.1).symm
  have ha0₃ : a₃ ≠ 0 := ((hypercubicLattice d).ne_of_adj hadj.2.2).symm
  
  have hGempty : (bc23_walkEdges (Walk.nil : (hypercubicLattice d).Walk a₁ a₁)
      ∪ bc23_walkEdges (Walk.nil : (hypercubicLattice d).Walk a₂ a₂)
      ∪ bc23_walkEdges (Walk.nil : (hypercubicLattice d).Walk a₃ a₃))
      = (∅ : Finset (Sym2 (Site d))) := by
    simp [bc23_walkEdges]
  
  set ϱ := removeSite 0 (forceOpenFinset (bc23_walkEdges (Walk.nil : (hypercubicLattice d).Walk a₁ a₁)
      ∪ bc23_walkEdges (Walk.nil : (hypercubicLattice d).Walk a₂ a₂)
      ∪ bc23_walkEdges (Walk.nil : (hypercubicLattice d).Walk a₃ a₃)) ω) with hϱ
  have hϱeq : ϱ = removeSite 0 ω := by rw [hϱ, hGempty, mng_forceOpenFinset_empty]
  
  have hcd12 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ :=
    bc20_removeSite_cluster_ne ω a₁ a₂ hdist.1
  have hcd13 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ :=
    bc20_removeSite_cluster_ne ω a₁ a₃ hdist.2.1
  have hcd23 : cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃ :=
    bc20_removeSite_cluster_ne ω a₂ a₃ hdist.2.2
  refine bc23_mengerCore_of_latticeCorridors ω a₁ a₂ a₃ a₁ a₂ a₃
    Walk.nil Walk.nil Walk.nil hne hadj (hw0 a₁ ha0₁) (hw0 a₂ ha0₂) (hw0 a₃ ha0₃) h0 hinf
    (cluster d ϱ a₁) (cluster d ϱ a₂) (cluster d ϱ a₃)
    (self_mem_cluster ϱ a₁) (self_mem_cluster ϱ a₂) (self_mem_cluster ϱ a₃)
    (fun u v hu hadj => mng_cluster_adjClosed ϱ a₁ hu hadj)
    (fun u v hu hadj => mng_cluster_adjClosed ϱ a₂ hu hadj)
    (fun u v hu hadj => mng_cluster_adjClosed ϱ a₃ hu hadj)
    ?_ ?_ ?_
  · rw [hϱeq]; exact mng_disjoint_of_cluster_ne (removeSite 0 ω) a₁ a₂ hcd12
  · rw [hϱeq]; exact mng_disjoint_of_cluster_ne (removeSite 0 ω) a₁ a₃ hcd13
  · rw [hϱeq]; exact mng_disjoint_of_cluster_ne (removeSite 0 ω) a₂ a₃ hcd23


end StatMech.Walls
