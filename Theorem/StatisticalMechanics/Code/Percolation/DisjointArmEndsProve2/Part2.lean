/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve2.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Def.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem daep2_globalCutSeparation_of_sameCluster (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daep2_SameClusterCutSeparation ω n) :
    daep_GlobalCutSeparation ω n := by
  classical
  obtain ⟨b, hb, hsame⟩ := h
  refine ⟨b, hb, ?_⟩
  intro x hxbox htri y hybox htriy hxy
  by_cases hconn : Connected d ω x y
  · 
    exact hsame x hxbox htri y hybox htriy hxy hconn
  · 
    obtain ⟨_, hbxconn, _⟩ := hb x hxbox htri
    obtain ⟨_, hbyconn, _⟩ := hb y hybox htriy
    exact daep2_crossCluster_branches_globalCut_disconnected (tfc_trifFinset ω n) ω
      hbxconn hbyconn hconn


theorem daep2_meets_at_most_one_branch (ω : ConfigSpace (Sym2 (Site d)))
    {x a₁ a₂ a₃ : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (v : Site d) :
    ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₂ v) ∧
    ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₃ v) ∧
    ¬ (Connected d (removeSite x ω) a₂ v ∧ Connected d (removeSite x ω) a₃ v) :=
  ⟨fun ⟨h1, h2⟩ => hd12 (h1.trans h2.symm),
   fun ⟨h1, h3⟩ => hd13 (h1.trans h3.symm),
   fun ⟨h2, h3⟩ => hd23 (h2.trans h3.symm)⟩


theorem daep2_two_branches_avoid (ω : ConfigSpace (Sym2 (Site d)))
    {x a₁ a₂ a₃ : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (v : Site d) :
    (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₂ v) ∨
    (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₃ v) ∨
    (¬ Connected d (removeSite x ω) a₂ v ∧ ¬ Connected d (removeSite x ω) a₃ v) := by
  classical
  by_cases h1 : Connected d (removeSite x ω) a₁ v
  · 
    refine Or.inr (Or.inr ⟨fun h2 => hd12 (h1.trans h2.symm), fun h3 => hd13 (h1.trans h3.symm)⟩)
  · by_cases h2 : Connected d (removeSite x ω) a₂ v
    · 
      exact Or.inr (Or.inl ⟨h1, fun h3 => hd23 (h2.trans h3.symm)⟩)
    · 
      exact Or.inl ⟨h1, h2⟩


end Percolation
end StatMech
