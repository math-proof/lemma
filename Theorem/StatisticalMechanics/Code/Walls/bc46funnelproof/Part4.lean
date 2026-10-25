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
import Def.StatisticalMechanics.Code.Walls.bc46funnelproof.Part3
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc46_parentFunneling_of_correctedParentGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc46_CorrectedParentGeometry ω n) : bc37_ParentFunneling ω n := by
  obtain ⟨b, hid, hdata, hclauses⟩ := hgeo
  
  have hdataC : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite := by
    intro x hxbox htri
    obtain ⟨hbox, hedge, hinf⟩ := hdata x hxbox htri
    exact ⟨hbox, hedge.connected, hinf⟩
  refine ⟨b, bc45_armDepthRank ω n, bc45_armForestPar ω n, hdataC,
    bc45_armDepthRank_injective ω n, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hparT, hpadj, hprank⟩ :=
    bc45_rooting_spec ω n x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hloc, hself, hmiss⟩ := hclauses x hxbox htri y hybox htriy hxy hconn hlt
  refine ⟨hloc, hself, fun hxne => ?_⟩
  
  have hxT : x ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
  have hyT : y ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
  
  have hrs : Connected d (removeSite y ω) x (bc45_armForestPar ω n y) :=
    bc45_rootWard_connected ω n hxT hyT hxy hconn hlt hpadj hparT hprank
  
  have hbxy : b x ≠ y := hmiss hxne
  obtain ⟨_, hedge, _⟩ := hdata x hxbox htri
  have hlink : Connected d (removeSite y ω) x (b x) :=
    bc46_armLink_survives y ω (Ne.symm hxy) (Ne.symm hbxy) hedge
  
  exact hlink.symm.trans hrs


theorem bc46_selfDownArm_of_correctedParentGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc46_CorrectedParentGeometry ω n) : bc36_SelfDownArm ω n :=
  bc37_selfDownArm_of_parentFunneling ω n
    (bc46_parentFunneling_of_correctedParentGeometry ω n hgeo)


theorem bc46_burton_keane_bernoulli_of_correctedParentGeometry (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      bc46_CorrectedParentGeometry ω n)
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
  bc36_burton_keane_bernoulli_of_selfDownArm hd p hp1 hp0
    (fun ω n hn => bc46_selfDownArm_of_correctedParentGeometry ω n (hgeo ω n hn)) htrif


theorem bc46_correctedParentGeometry_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc46_CorrectedParentGeometry ω n := by
  refine ⟨id, fun _ _ => rfl, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)


end StatMech.Walls
