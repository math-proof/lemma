/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SpanForestArmsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
import Def.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part2
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem ctc2_canonTcount_le_Tcount (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    ctc2_canonTcount d ω n ≤ Tcount d ω n := by
  classical
  unfold ctc2_canonTcount Tcount
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, ctc2_isTrifurcation_of_canonical hx.2⟩


theorem ctc2_canonTcount_le_boundary_of_forestLeafInjection (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : daec_ForestLeafInjection ω n) :
    ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d n :=
  le_trans (ctc2_canonTcount_le_Tcount ω n) (ctc2_count_of_forestLeafInjection ω n h)


theorem ctc2_canonTcount_le_boundary_of_subsingleton (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n)
    (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n →
      IsTrifurcation d ω y → x = y) :
    ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d n :=
  le_trans (ctc2_canonTcount_le_Tcount ω n) (ctc2_count_of_subsingleton ω n hn hsub)


end Percolation
end StatMech
