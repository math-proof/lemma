/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc22trifexist.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc20mengerroute.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc21trifurc.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneAttachment.Part4
import Def.StatisticalMechanics.Code.Walls.bc22trifexist
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech.Walls

variable {d : ℕ}


universe u

variable {V : Type u} {GG : SimpleGraph V}


theorem bc22_mengerCore_of_mergeFree (ω : ConfigSpace (Sym2 (Site d)))
    (h : bka_MergeFree ω) : MengerCore ω := by
  obtain ⟨a₁, a₂, a₃, hne, hadj, hinf, hdist⟩ := h
  exact mng_mengerCore_of_neighborClusters ω a₁ a₂ a₃ hne hadj hinf hdist


theorem bc22_mengerRoutingCover_of_boxThreeBranchMinCut (d n : ℕ)
    (h : bc22_BoxThreeBranchMinCut d n) : MengerRoutingCover d n :=
  fun ω hω => bc22_mengerCore_of_mergeFree ω (h ω hω)


theorem bc22_burtonKeane_uniqueness_of_boxThreeBranchMinCut
    (μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site d))))
    [MeasureTheory.IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hr : ∀ n : ℕ, bc22_BoxThreeBranchMinCut d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  mng_burton_keane_uniqueness_mengerCover μ herg hfe bdry hbound hvol hdens
    (fun n => bc22_mengerRoutingCover_of_boxThreeBranchMinCut d n (hr n))


theorem bc22_mergeFree_of_threeBranchPaths (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ b₁ b₂ b₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hconn : Connected d (removeSite 0 ω) a₁ b₁ ∧ Connected d (removeSite 0 ω) a₂ b₂ ∧
      Connected d (removeSite 0 ω) a₃ b₃)
    (h0 : (0 : Site d) ∉ cluster d ω b₁ ∧ (0 : Site d) ∉ cluster d ω b₂ ∧
      (0 : Site d) ∉ cluster d ω b₃)
    (hinf : (cluster d ω b₁).Infinite ∧ (cluster d ω b₂).Infinite ∧ (cluster d ω b₃).Infinite)
    (hdist : cluster d ω b₁ ≠ cluster d ω b₂ ∧ cluster d ω b₁ ≠ cluster d ω b₃ ∧
      cluster d ω b₂ ≠ cluster d ω b₃) :
    bka_MergeFree ω := by
  
  have hclA₁ : cluster d (removeSite 0 ω) a₁ = cluster d (removeSite 0 ω) b₁ :=
    cluster_eq_of_connected hconn.1
  have hclA₂ : cluster d (removeSite 0 ω) a₂ = cluster d (removeSite 0 ω) b₂ :=
    cluster_eq_of_connected hconn.2.1
  have hclA₃ : cluster d (removeSite 0 ω) a₃ = cluster d (removeSite 0 ω) b₃ :=
    cluster_eq_of_connected hconn.2.2
  
  have hbi₁ : (cluster d (removeSite 0 ω) b₁).Infinite :=
    bc20_removeSite_infinite_of_originFree ω b₁ h0.1 hinf.1
  have hbi₂ : (cluster d (removeSite 0 ω) b₂).Infinite :=
    bc20_removeSite_infinite_of_originFree ω b₂ h0.2.1 hinf.2.1
  have hbi₃ : (cluster d (removeSite 0 ω) b₃).Infinite :=
    bc20_removeSite_infinite_of_originFree ω b₃ h0.2.2 hinf.2.2
  
  have hbd₁₂ : cluster d (removeSite 0 ω) b₁ ≠ cluster d (removeSite 0 ω) b₂ :=
    bc20_removeSite_cluster_ne ω b₁ b₂ hdist.1
  have hbd₁₃ : cluster d (removeSite 0 ω) b₁ ≠ cluster d (removeSite 0 ω) b₃ :=
    bc20_removeSite_cluster_ne ω b₁ b₃ hdist.2.1
  have hbd₂₃ : cluster d (removeSite 0 ω) b₂ ≠ cluster d (removeSite 0 ω) b₃ :=
    bc20_removeSite_cluster_ne ω b₂ b₃ hdist.2.2
  exact ⟨a₁, a₂, a₃, hne, hadj,
    ⟨hclA₁ ▸ hbi₁, hclA₂ ▸ hbi₂, hclA₃ ▸ hbi₃⟩,
    ⟨hclA₁ ▸ hclA₂ ▸ hbd₁₂, hclA₁ ▸ hclA₃ ▸ hbd₁₃, hclA₂ ▸ hclA₃ ▸ hbd₂₃⟩⟩


theorem bc22_mergeFree_of_originFree (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (h0 : (0 : Site d) ∉ cluster d ω a₁ ∧ (0 : Site d) ∉ cluster d ω a₂ ∧
      (0 : Site d) ∉ cluster d ω a₃)
    (hinf : (cluster d ω a₁).Infinite ∧ (cluster d ω a₂).Infinite ∧ (cluster d ω a₃).Infinite)
    (hdist : cluster d ω a₁ ≠ cluster d ω a₂ ∧ cluster d ω a₁ ≠ cluster d ω a₃ ∧
      cluster d ω a₂ ≠ cluster d ω a₃) :
    bka_MergeFree ω :=
  bc22_mergeFree_of_threeBranchPaths ω a₁ a₂ a₃ a₁ a₂ a₃ hne hadj
    ⟨connected_rfl, connected_rfl, connected_rfl⟩ h0 hinf hdist


theorem bc22_mengerCore_of_originFree (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (h0 : (0 : Site d) ∉ cluster d ω a₁ ∧ (0 : Site d) ∉ cluster d ω a₂ ∧
      (0 : Site d) ∉ cluster d ω a₃)
    (hinf : (cluster d ω a₁).Infinite ∧ (cluster d ω a₂).Infinite ∧ (cluster d ω a₃).Infinite)
    (hdist : cluster d ω a₁ ≠ cluster d ω a₂ ∧ cluster d ω a₁ ≠ cluster d ω a₃ ∧
      cluster d ω a₂ ≠ cluster d ω a₃) :
    MengerCore ω :=
  bc22_mengerCore_of_mergeFree ω (bc22_mergeFree_of_originFree ω a₁ a₂ a₃ hne hadj h0 hinf hdist)


theorem bc22_subfamily_avoiding_nonvacuous {A B : Set V} {k : ℕ}
    (F : bc16_DisjointPathFamily GG A B (Fin (k + 1))) (z₀ : V) :
    ∃ G : bc16_DisjointPathFamily GG A B (Fin k), ∀ i : Fin k, z₀ ∉ (G.p i).support :=
  bc22_subfamily_avoiding F z₀


theorem bc22_mengerCore_of_mergeFree' (ω : ConfigSpace (Sym2 (Site d)))
    (h : bka_MergeFree ω) : MengerCore ω :=
  bc22_mengerCore_of_mergeFree ω h


end StatMech.Walls
