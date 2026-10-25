/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosingLength.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Def.StatisticalMechanics.Code.Lattice.EnclosingLength
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Percolation (anchorFinset origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem anchoredCycleExists_of_leftFace (hfin : (cluster 2 ω (origin 2)).Finite)
    (hlf : CycleHasLeftFace ω hfin) : AnchoredCycleExists ω hfin := by
  obtain ⟨c, hcyc, w, hwsup, hw0⟩ := hlf
  refine ⟨c, hcyc, ?_⟩
  rcases Nat.eq_zero_or_pos (exitIndex (ω := ω) hfin) with hj | hj
  · 
    rw [hj]
    exact lt_of_lt_of_le (by norm_num) hcyc.three_le_length
  · 
    have hge : 2 * l1dist 2 (exitFaceUp (ω := ω) hfin) w ≤ c.length :=
      closedWalk_length_ge_two_l1dist (faceBoundaryGraph_le _) c hwsup
    have hdist : (exitIndex (ω := ω) hfin : ℕ) ≤ l1dist 2 (exitFaceUp (ω := ω) hfin) w :=
      exitIndex_le_l1dist_of_leftFace (ω := ω) hfin hw0
    omega


theorem anchoredEnclosure_of_cycleHasLeftFace (hfin : (cluster 2 ω (origin 2)).Finite)
    (hlf : CycleHasLeftFace ω hfin) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk u u),
      c.IsCycle ∧ u ∈ anchorFinset c.length :=
  anchoredEnclosure_of_anchoredCycle (ω := ω) hfin
    (anchoredCycleExists_of_leftFace (ω := ω) hfin hlf)


theorem pcAnchoredEnclosure_of_cycleHasLeftFace
    (hlf : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        CycleHasLeftFace ω hfin) :
    StatMech.Percolation.PcAnchoredEnclosure := by
  intro ω hω
  exact anchoredEnclosure_of_cycleHasLeftFace (ω := ω) hω (hlf ω hω)


end Lattice
end StatMech
