/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc24coarsetrif.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc21trifurc.Part2
open Set SimpleGraph MeasureTheory
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc24_cluster_ne_of_not_connected {σ : ConfigSpace (Sym2 (Site d))} {a b : Site d}
    (h : ¬ Connected d σ a b) : cluster d σ a ≠ cluster d σ b := by
  intro heq
  exact h (mem_cluster.mp (heq ▸ self_mem_cluster σ b))


theorem bc24_box_merges_infinite {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n) :
    cluster d (forceOpenFinset (boxEdges d n) ω) x
      = cluster d (forceOpenFinset (boxEdges d n) ω) y :=
  box_allOpen_cluster_eq ω hx hy


theorem bc24_arm_connected_box {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {a b z : Site d} (hb : b ∈ box d n) (hz : z ∈ box d n)
    (hab : Connected d ω a b) :
    Connected d (forceOpenFinset (boxEdges d n) ω) a z := by
  
  have hab' : Connected d (forceOpenFinset (boxEdges d n) ω) a b :=
    connected_mono (forceOpenFinset_le _ ω) hab
  
  exact hab'.trans (box_allOpen_connected ω hb hz)


theorem bc24_armEnds_connected_through_box {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {a₁ a₂ a₃ b₁ b₂ b₃ : Site d}
    (hb₁ : b₁ ∈ box d n) (hb₂ : b₂ ∈ box d n) (hb₃ : b₃ ∈ box d n)
    (h₁ : Connected d ω a₁ b₁) (h₂ : Connected d ω a₂ b₂) (h₃ : Connected d ω a₃ b₃) :
    Connected d (forceOpenFinset (boxEdges d n) ω) a₁ a₂ ∧
      Connected d (forceOpenFinset (boxEdges d n) ω) a₁ a₃ ∧
      Connected d (forceOpenFinset (boxEdges d n) ω) a₂ a₃ := by
  
  have c1 : Connected d (forceOpenFinset (boxEdges d n) ω) a₁ b₁ :=
    bc24_arm_connected_box ω hb₁ hb₁ h₁
  have c2 : Connected d (forceOpenFinset (boxEdges d n) ω) a₂ b₁ :=
    bc24_arm_connected_box ω hb₂ hb₁ h₂
  have c3 : Connected d (forceOpenFinset (boxEdges d n) ω) a₃ b₁ :=
    bc24_arm_connected_box ω hb₃ hb₁ h₃
  exact ⟨c1.trans c2.symm, c1.trans c3.symm, c2.trans c3.symm⟩


end StatMech.Walls
