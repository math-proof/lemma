/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestPathStructure.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.ForestAcyclicityClose.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem fps_cutX_sep_of_privateFar_x (ω : ConfigSpace (Sym2 (Site d))) {x bx by_ y : Site d}
    (hpriv : ¬ Connected d (removeSite x ω) bx y)
    (hfar : Connected d (removeSite x ω) by_ y) :
    ¬ Connected d (removeSite x ω) bx by_ := by
  intro hbxby
  exact hpriv (hbxby.trans hfar)


theorem fps_cutY_sep_of_privateFar_y (ω : ConfigSpace (Sym2 (Site d))) {y bx by_ x : Site d}
    (hpriv : ¬ Connected d (removeSite y ω) by_ x)
    (hfar : Connected d (removeSite y ω) bx x) :
    ¬ Connected d (removeSite y ω) bx by_ := by
  intro hbxby
  exact hpriv (hbxby.symm.trans hfar)


theorem fps_eitherCut_sep_of_twoSidedPrivateFar (ω : ConfigSpace (Sym2 (Site d)))
    {x y bx by_ : Site d}
    (hprivx : ¬ Connected d (removeSite x ω) bx y)
    (hprivy : ¬ Connected d (removeSite y ω) by_ x)
    (hfar : Connected d (removeSite x ω) by_ y ∨ Connected d (removeSite y ω) bx x) :
    ¬ Connected d (removeSite x ω) bx by_ ∨ ¬ Connected d (removeSite y ω) bx by_ := by
  rcases hfar with hfarx | hfary
  · 
    exact Or.inl (fps_cutX_sep_of_privateFar_x ω hprivx hfarx)
  · 
    exact Or.inr (fps_cutY_sep_of_privateFar_y ω hprivy hfary)


end Percolation
end StatMech
