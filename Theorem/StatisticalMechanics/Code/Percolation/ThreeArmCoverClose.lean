/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ThreeArmCoverClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Theorem.StatisticalMechanics.Code.Percolation.ForestColouringClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BKHallSDRClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose.Part4
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem tac_not_threeArmCover_of_fourArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {y : Site d} (hybox : y ∈ box d n) (htri : IsTrifurcation d ω y)
    (c : Fin 4 → Site d)
    (hconn : ∀ k, Connected d ω y (c k)) (hne : ∀ k, y ≠ c k)
    (hdis : ∀ k l, k ≠ l → ¬ Connected d (removeSite y ω) (c k) (c l)) :
    ¬ fcc_ThreeArmCover ω n := by
  classical
  rintro ⟨arms, harms⟩
  obtain ⟨hsep, hcover⟩ := harms y hybox htri
  
  choose i hi using fun k => hcover (c k) (hconn k) (hne k)
  
  obtain ⟨k, l, hkl, hcol⟩ := Fintype.exists_ne_map_eq_of_card_lt i (by simp)
  
  have hwit_kl : Connected d (removeSite y ω)
      (fsp_armWitness ω y (c k)) (fsp_armWitness ω y (c l)) := by
    have h1 := hi k
    have h2 := hi l
    rw [hcol] at h1
    exact h1.symm.trans h2
  
  have hck : Connected d (removeSite y ω) (fsp_armWitness ω y (c k)) (c k) :=
    fsp_armWitness_inArm ω (hconn k) (hne k)
  have hcl : Connected d (removeSite y ω) (fsp_armWitness ω y (c l)) (c l) :=
    fsp_armWitness_inArm ω (hconn l) (hne l)
  exact hdis k l hkl (hck.symm.trans (hwit_kl.trans hcl))


end Percolation
end StatMech
