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
import Def.StatisticalMechanics.Code.Percolation.BKForestLib
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem bkfl_inArm_self (ω : ConfigSpace (Sym2 (Site d))) (x a : Site d) :
    bkfl_inArm ω x a a := connected_rfl

theorem bkfl_inArm_symm_witness (ω : ConfigSpace (Sym2 (Site d))) {x a a' v : Site d}
    (haa' : Connected d (removeSite x ω) a a') (h : bkfl_inArm ω x a v) :
    bkfl_inArm ω x a' v := haa'.symm.trans h


theorem bkfl_sameArm_connected (ω : ConfigSpace (Sym2 (Site d))) {x a u v : Site d}
    (hu : bkfl_inArm ω x a u) (hv : bkfl_inArm ω x a v) :
    Connected d (removeSite x ω) u v := hu.symm.trans hv


theorem bkfl_arms_separate (ω : ConfigSpace (Sym2 (Site d))) {x a b u w : Site d}
    (hdis : ¬ Connected d (removeSite x ω) a b)
    (hu : bkfl_inArm ω x a u) (hw : bkfl_inArm ω x b w) :
    ¬ Connected d (removeSite x ω) u w := by
  intro huw
  
  exact hdis (hu.trans (huw.trans hw.symm))


theorem bkfl_atMostOneArm (ω : ConfigSpace (Sym2 (Site d))) {x a₁ a₂ a₃ v : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
    ¬ (bkfl_inArm ω x a₁ v ∧ bkfl_inArm ω x a₂ v) ∧
    ¬ (bkfl_inArm ω x a₁ v ∧ bkfl_inArm ω x a₃ v) ∧
    ¬ (bkfl_inArm ω x a₂ v ∧ bkfl_inArm ω x a₃ v) :=
  ⟨fun ⟨h1, h2⟩ => bkfl_arms_separate ω hd12 h1 h2 connected_rfl,
   fun ⟨h1, h3⟩ => bkfl_arms_separate ω hd13 h1 h3 connected_rfl,
   fun ⟨h2, h3⟩ => bkfl_arms_separate ω hd23 h2 h3 connected_rfl⟩


end Percolation
end StatMech
