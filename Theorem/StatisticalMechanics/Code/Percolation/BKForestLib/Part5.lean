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
import Def.StatisticalMechanics.Code.Percolation.BKForestLib.Part5
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem bkfl_free_of_unoccupied (ω : ConfigSpace (Sym2 (Site d))) (T : Finset (Site d))
    {x a : Site d} (h : ¬ bkfl_Occupied ω T x a) :
    ∀ y ∈ T, y ≠ x → ¬ Connected d (removeSite x ω) a y := by
  intro y hyT hyx hc
  exact h ⟨y, hyT, hyx, hc⟩


theorem bkfl_pointwise_of_unoccupiedArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (T : Finset (Site d)) {x a : Site d}
    (hdata : a ∈ box d n ∧ Connected d ω x a ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) a).Infinite)
    (hunocc : ¬ bkfl_Occupied ω T x a)
    (hfar : ∀ z ∈ T, z ≠ x → Connected d (removeSite z ω) a x) :
    bkfl_PointwisePrivateFar ω n T x a :=
  ⟨hdata, bkfl_free_of_unoccupied ω T hunocc, hfar⟩


theorem bkfl_exists_unoccupied_arm (ω : ConfigSpace (Sym2 (Site d))) (T : Finset (Site d))
    {x a₁ a₂ a₃ : Site d}
    (hsome : ¬ bkfl_Occupied ω T x a₁ ∨ ¬ bkfl_Occupied ω T x a₂ ∨
      ¬ bkfl_Occupied ω T x a₃) :
    ∃ a ∈ ({a₁, a₂, a₃} : Finset (Site d)), ¬ bkfl_Occupied ω T x a := by
  classical
  rcases hsome with h1 | h2 | h3
  · exact ⟨a₁, by simp, h1⟩
  · exact ⟨a₂, by simp, h2⟩
  · exact ⟨a₃, by simp, h3⟩


theorem bkfl_sameArm_occupants_connected (ω : ConfigSpace (Sym2 (Site d)))
    {x a y y' : Site d}
    (hy : Connected d (removeSite x ω) a y) (hy' : Connected d (removeSite x ω) a y') :
    Connected d (removeSite x ω) y y' := hy.symm.trans hy'


end Percolation
end StatMech
