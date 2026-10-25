/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestSelectorProve.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.PrivateArmProve.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Def.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part5
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem fsp_sep_of_notSameArm (ω : ConfigSpace (Sym2 (Site d))) {x u v : Site d}
    (hxu : Connected d ω x u) (hneu : x ≠ u)
    (hxv : Connected d ω x v) (hnev : x ≠ v)
    (hdiv : ¬ fsp_sameArm ω x u v) :
    ¬ Connected d (removeSite x ω) u v := by
  intro huv
  
  exact hdiv ((fsp_armWitness_inArm ω hxu hneu).trans
    (huv.trans (fsp_armWitness_inArm ω hxv hnev).symm))


theorem fsp_armPlacement_of_divergentWitness (ω : ConfigSpace (Sym2 (Site d)))
    (b : Site d → Site d) {x y a c : Site d}
    (hdis : ¬ Connected d (removeSite x ω) a c)
    (hbx : bkfl_inArm ω x a (b x)) (hby : bkfl_inArm ω x c (b y)) :
    fsp_ArmPlacement ω b x y := ⟨a, c, hdis, hbx, hby⟩


theorem fsp_inArm_of_witness (ω : ConfigSpace (Sym2 (Site d))) {x a v : Site d}
    (h : Connected d (removeSite x ω) a v) : bkfl_inArm ω x a v := h


theorem fsp_inArm_self (ω : ConfigSpace (Sym2 (Site d))) (x a : Site d) :
    bkfl_inArm ω x a a := bkfl_inArm_self ω x a


end Percolation
end StatMech
