/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsClose.lean -/

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
import Def.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem daec_forestLeafInjection_iff_distinctArmEnds (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) : daec_ForestLeafInjection ω n ↔ tfc_DistinctArmEnds ω n := Iff.rfl


theorem daec_distinctArmEnds_of_forestLeafInjection (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : daec_ForestLeafInjection ω n) : tfc_DistinctArmEnds ω n := h


theorem daec_forestLeafInjection_of_subsingleton (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n)
    (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n →
      IsTrifurcation d ω y → x = y) :
    daec_ForestLeafInjection ω n :=
  tfc_distinctArmEnds_of_subsingleton ω n hn hsub


theorem daec_Tcount_le_boundary_of_forestLeafInjection (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : daec_ForestLeafInjection ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  tfc_Tcount_le_boundary_of_distinctArmEnds ω n h


theorem daec_forestLeafInjection_of_disjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hdisj : bk2_DisjointArmEnds ω n) :
    daec_ForestLeafInjection ω n :=
  bk2_distinctArmEnds_of_disjoint ω n hn hdisj


theorem daec_burton_keane_bernoulli (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      daec_ForestLeafInjection ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  tfc_burton_keane_bernoulli hd p hp1 hp0
    (fun ω n hn => daec_distinctArmEnds_of_forestLeafInjection ω n (hres ω n hn))
    htrif

end Percolation
end StatMech
