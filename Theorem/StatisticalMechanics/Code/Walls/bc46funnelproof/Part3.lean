/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc40funnel.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc45depthwalk.Part4
import Def.StatisticalMechanics.Code.Walls.bc46funnelproof.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc46_armFunnelGeometry_of_neighborArmFunnel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc46_NeighborArmFunnel ω n) : bc46_ArmFunnelGeometry ω n := by
  obtain ⟨b, hid, hdata, hclauses⟩ := hgeo
  refine ⟨b, ?_, ?_⟩
  · 
    intro x hxbox htri
    obtain ⟨hbox, hedge, hinf⟩ := hdata x hxbox htri
    exact ⟨hbox, hedge.connected, hinf⟩
  · intro t s htbox htri hadj
    obtain ⟨hloc, hself, hmiss⟩ := hclauses t s htbox htri hadj
    refine ⟨hloc, hself, ?_⟩
    intro x hxt hxs
    by_cases hxtri : x ∈ box d n ∧ IsTrifurcation d ω x
    · 
      obtain ⟨_, hedge, _⟩ := hdata x hxtri.1 hxtri.2
      have hbxt : b x ≠ t := hmiss x hxtri.1 hxtri.2 hxt hxs
      exact bc46_armLink_survives t ω (Ne.symm hxt) (Ne.symm hbxt) hedge
    · 
      rw [hid x hxtri]


theorem bc46_parentFunneling_of_armFunnelGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc46_ArmFunnelGeometry ω n) : bc37_ParentFunneling ω n :=
  bc45_parentFunneling_of_cutGeometryFixed' ω n
    (bc46_armCutGeometryFixed'_of_armFunnelGeometry ω n hgeo)


theorem bc46_selfDownArm_of_armFunnelGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc46_ArmFunnelGeometry ω n) : bc36_SelfDownArm ω n :=
  bc45_selfDownArm_of_cutGeometryFixed' ω n
    (bc46_armCutGeometryFixed'_of_armFunnelGeometry ω n hgeo)


theorem bc46_burton_keane_bernoulli_of_armFunnelGeometry (hd : 1 ≤ d) (p : NNReal)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc46_ArmFunnelGeometry ω n)
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
  bc45_burton_keane_bernoulli hd p hp1 hp0
    (fun ω n hn => bc46_armCutGeometryFixed'_of_armFunnelGeometry ω n (hgeo ω n hn)) htrif


theorem bc46_burton_keane_bernoulli_of_neighborArmFunnel (hd : 1 ≤ d) (p : NNReal)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc46_NeighborArmFunnel ω n)
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
  bc46_burton_keane_bernoulli_of_armFunnelGeometry hd p hp1 hp0
    (fun ω n hn => bc46_armFunnelGeometry_of_neighborArmFunnel ω n (hgeo ω n hn)) htrif


end StatMech.Walls
