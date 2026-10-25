/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestAcyclicityClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BKHallSDRClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem fac_singleCut_of_globalCut (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    {z u v : Site d} (hzT : z ∈ T) (h : Connected d (removeSites T ω) u v) :
    Connected d (removeSite z ω) u v :=
  connected_mono (daep2_removeSites_le_removeSite T ω hzT) h


theorem fac_globalDisc_of_singleDisc (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    {z u v : Site d} (hzT : z ∈ T) (h : ¬ Connected d (removeSite z ω) u v) :
    ¬ Connected d (removeSites T ω) u v :=
  fun hc => h (fac_singleCut_of_globalCut T ω hzT hc)


theorem fac_trif_mem_finset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {x : Site d}
    (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x) :
    x ∈ tfc_trifFinset ω n :=
  tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩


theorem fac_globalSep_of_eitherCut (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x y u v : Site d} (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x)
    (hybox : y ∈ box d n) (htriy : IsTrifurcation d ω y)
    (h : ¬ Connected d (removeSite x ω) u v ∨ ¬ Connected d (removeSite y ω) u v) :
    ¬ Connected d (removeSites (tfc_trifFinset ω n) ω) u v := by
  rcases h with hx | hy
  · exact fac_globalDisc_of_singleDisc _ ω (fac_trif_mem_finset ω n hxbox htri) hx
  · exact fac_globalDisc_of_singleDisc _ ω (fac_trif_mem_finset ω n hybox htriy) hy


end Percolation
end StatMech
