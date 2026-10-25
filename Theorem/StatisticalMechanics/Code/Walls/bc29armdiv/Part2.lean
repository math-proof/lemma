/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc29armdiv.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKArmSelectorClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc28forestroot.Part2
import Def.StatisticalMechanics.Code.Walls.bc29armdiv
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc29_armDivergenceForRank_of_rootedDownArmForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (h : bc29_RootedDownArmForest ω n rank) :
    bc28_ArmDivergenceForRank ω n rank := by
  obtain ⟨b, hbdata, hsplit⟩ := h
  refine ⟨b, hbdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  
  have hsp : ¬ Connected d (removeSite y ω) (b y) (b x) :=
    hsplit x hxbox htri y hybox htriy hxy hconn hlt
  
  set T := tfc_trifFinset ω n with hT
  have hyT : y ∈ T := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
  have hbxnotin : b x ∉ T :=
    stac_infiniteCluster_notMem T ω (hbdata x hxbox htri).2.2
  have hbynotin : b y ∉ T :=
    stac_infiniteCluster_notMem T ω (hbdata y hybox htriy).2.2
  have hne_y_bx : y ≠ b x := fun heq => hbxnotin (heq ▸ hyT)
  have hne_y_by : y ≠ b y := fun heq => hbynotin (heq ▸ hyT)
  
  have hy_bx : Connected d ω y (b x) := hconn.symm.trans (hbdata x hxbox htri).2.1
  have hy_by : Connected d ω y (b y) := (hbdata y hybox htriy).2.1
  exact bc29_notSameArm_of_armSplit ω hy_bx hne_y_bx hy_by hne_y_by hsp


theorem bc29_rootedArmDivergence_of_rootedDownArmForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ)
    (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y)
    (h : bc29_RootedDownArmForest ω n rank) :
    rfp_RootedArmDivergence ω n :=
  bc28_rootedArmDivergence_of_armDivergenceForRank ω n rank hinj
    (bc29_armDivergenceForRank_of_rootedDownArmForest ω n rank h)


end StatMech.Walls
