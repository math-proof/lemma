/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKForestLib.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsFinal.Part2
import Def.StatisticalMechanics.Code.Percolation.BKForestLib.Part3
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem bkfl_privateArm_of_coherentSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bkfl_CoherentArmSelector ω n) : daepf_PrivateArm ω n := by
  obtain ⟨b, hdata, hpair⟩ := h
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    exact hdata x hxbox htri
  · intro x hxbox htri y hybox htriy hxy hconn
    obtain ⟨hpriv, hfar⟩ := hpair x hxbox htri y hybox htriy hxy hconn
    exact ⟨hpriv, hfar⟩


theorem bkfl_singleCutBranchSeparation_of_coherentSelector
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (h : bkfl_CoherentArmSelector ω n) :
    daep2_SingleCutBranchSeparation ω n :=
  daepf_singleCutBranchSeparation_of_privateArm ω n
    (bkfl_privateArm_of_coherentSelector ω n h)


theorem bkfl_Tcount_le_boundary_of_coherentSelector (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) (h : bkfl_CoherentArmSelector ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daepf_Tcount_le_boundary_of_privateArm ω n hn
    (bkfl_privateArm_of_coherentSelector ω n h)


end Percolation
end StatMech
