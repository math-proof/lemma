/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LeafHallClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeRealiseClose.Part2
import Def.StatisticalMechanics.Code.Percolation.LeafHallClose.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem lhc_not_forestLeafSelection_of_clawTrace (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hclaw : lhc_ConnectedClawTrace ω n) :
    ¬ str_ForestLeafSelection ω n := by
  rintro h
  obtain ⟨x₀, hconn, hsmall⟩ := hclaw
  have hge := lhc_two_le_trace_of_forestLeafSelection ω n x₀ hconn h
  omega


theorem lhc_clawTrace_excludes_forestLeafSelection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hclaw : lhc_ConnectedClawTrace ω n) (h : str_ForestLeafSelection ω n) : False :=
  lhc_not_forestLeafSelection_of_clawTrace ω n hclaw h


theorem lhc_clawTrace_card_consistent {T : ℕ} (hT : 3 ≤ T) :
    T + 2 ≤ T + 2 ∧ T + 2 < 2 * T :=
  ⟨le_refl _, by omega⟩


theorem lhc_clawTrace_of_smallTrace (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x₀ : Site d)
    (hconn : ∀ x, x ∈ box d n → IsTrifurcation d ω x → Connected d ω x₀ x)
    (hsmall : (lhc_trace ω n x₀).card < 2 * Tcount d ω n) :
    lhc_ConnectedClawTrace ω n :=
  ⟨x₀, hconn, hsmall⟩


theorem lhc_boundaryArmInjection_of_forestLeafSelection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : str_ForestLeafSelection ω n) :
    tfc_BoundaryArmInjection ω n := by
  obtain ⟨r₀, ℓ, _hr₀, hℓbdry, _hℓconn, _hℓr₀, hℓinj⟩ := h
  refine ⟨fun x => ℓ x 0, ?_, ?_⟩
  · intro x hxbox htri; exact hℓbdry x hxbox htri 0
  · intro x hxbox htri y hybox htriy hxy
    exact (hℓinj x hxbox htri y hybox htriy 0 0 hxy).1


theorem lhc_Tcount_le_boundary_of_boundaryArmInjection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : tfc_BoundaryArmInjection ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  tfc_Tcount_le_boundary_of_residue ω n h


theorem lhc_Tcount_le_boundary_of_forestLeafSelection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : str_ForestLeafSelection ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  lhc_Tcount_le_boundary_of_boundaryArmInjection ω n
    (lhc_boundaryArmInjection_of_forestLeafSelection ω n h)


theorem lhc_boundaryArmInjection_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {r a : Site d} (ha : a ∈ vertexBoundary d n)
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = r) :
    tfc_BoundaryArmInjection ω n := by
  refine ⟨fun _ => a, fun x _ _ => ha, ?_⟩
  intro x hxbox htri y hybox htriy _
  exact (hsingle x hxbox htri).trans (hsingle y hybox htriy).symm


theorem lhc_burton_keane_bernoulli_of_boundaryArmInjection (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → tfc_BoundaryArmInjection ω n)
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
  tfc_burton_keane_uniqueness_full (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
    (bkc_bernoulli_isErgodic hd p hp1)
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0)
    (fun n => boxSV_boundaryCard d n)
    (fun ω n hn => lhc_Tcount_le_boundary_of_boundaryArmInjection ω n (hres ω n hn))
    (fun n => bkc_boxFinsetBK_card_pos d n)
    (bkc_boundary_vol_tendsto d hd)
    htrif

end Percolation
end StatMech
