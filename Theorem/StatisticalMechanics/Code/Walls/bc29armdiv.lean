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
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc29_notSameArm_of_armSplit (ω : ConfigSpace (Sym2 (Site d)))
    {y bx by' : Site d}
    (hy_bx : Connected d ω y bx) (hne_bx : y ≠ bx)
    (hy_by : Connected d ω y by') (hne_by : y ≠ by')
    (hsplit : ¬ Connected d (removeSite y ω) by' bx) :
    ¬ fsp_sameArm ω y bx by' := by
  intro hsame
  
  
  
  have hwbx : Connected d (removeSite y ω) (fsp_armWitness ω y bx) bx :=
    fsp_armWitness_inArm ω hy_bx hne_bx
  have hwby : Connected d (removeSite y ω) (fsp_armWitness ω y by') by' :=
    fsp_armWitness_inArm ω hy_by hne_by
  
  exact hsplit ((hwby.symm.trans hsame.symm).trans hwbx)


theorem bc29_armSplit_consistent :
    ∃ (ω : ConfigSpace (Sym2 (Site 1))) (y bx by' : Site 1),
      ¬ Connected 1 (removeSite y ω) by' bx :=
  ⟨rfp_ωpath, rfp_p1, rfp_p2, rfp_p0, fun h => rfp_consistency_crossed h.symm⟩


theorem bc29_multiAncestorSplit_consistent :
    ∃ (ω : ConfigSpace (Sym2 (Site 1))) (y bx₁ bx₂ by' : Site 1),
      ¬ Connected 1 (removeSite y ω) by' bx₁ ∧ ¬ Connected 1 (removeSite y ω) by' bx₂ :=
  ⟨rfp_ωpath, rfp_p1, rfp_p0, rfp_p0, rfp_p2,
    rfp_consistency_crossed, rfp_consistency_crossed⟩


end StatMech.Walls
