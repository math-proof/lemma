/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose2.lean -/

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
import Def.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem bk2_mem_armEndFinset {ω : ConfigSpace (Sym2 (Site d))} {n : ℕ} {x z : Site d} :
    z ∈ bk2_armEndFinset ω n x ↔ z ∈ vertexBoundary d n ∧ Connected d ω x z := by
  classical
  rw [bk2_armEndFinset, Finset.mem_filter, tfc_mem_boundaryFinset]


theorem bk2_armEndFinset_subset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x : Site d) :
    bk2_armEndFinset ω n x ⊆ tfc_boundaryFinset d n := by
  classical
  exact Finset.filter_subset _ _


theorem bk2_armEndFinset_nonempty (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (x : Site d) (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x) :
    (bk2_armEndFinset ω n x).Nonempty := by
  obtain ⟨z, hzb, hzc⟩ := tfc_trif_reaches_boundary ω n hn x hxbox htri
  exact ⟨z, bk2_mem_armEndFinset.mpr ⟨hzb, hzc⟩⟩


end Percolation
end StatMech
