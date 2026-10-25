/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/RootedForestPeelClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.FacPairwiseClose
import Theorem.StatisticalMechanics.Code.Percolation.BKArmSelectorClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.RootedTreeSelectorClose
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestColouringClose2.Part3
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem rfp_root_arm_obstruction (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {b : Site d → Site d} {rank : Site d → ℕ ×ₗ ℕ} {x₀ z : Site d}
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hzbox : z ∈ box d n) (htriz : IsTrifurcation d ω z)
    (hne : x₀ ≠ z) (hconn : Connected d ω x₀ z)
    (hrank : rank x₀ ≠ rank z)
    (hpair : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x < rank y →
      Connected d (removeSite y ω) (b x) x ∧ ¬ Connected d (removeSite y ω) (b y) x)
    (hbeyond : Connected d (removeSite x₀ ω) (b x₀) z)
    (hcrossed : ¬ Connected d (removeSite z ω) (b x₀) x₀) :
    False := by
  rcases lt_trichotomy (rank x₀) (rank z) with hlt | heq | hgt
  · 
    obtain ⟨hfar, _hpriv⟩ := hpair x₀ hx0box htri0 z hzbox htriz hne hconn hlt
    
    exact hcrossed hfar
  · exact hrank heq
  · 
    obtain ⟨_hfar, hpriv⟩ :=
      hpair z hzbox htriz x₀ hx0box htri0 hne.symm hconn.symm hgt
    
    exact hpriv hbeyond


end Percolation
end StatMech
