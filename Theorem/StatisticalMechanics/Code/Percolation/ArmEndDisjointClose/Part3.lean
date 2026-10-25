/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmEndDisjointClose.lean -/

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
import Def.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem aed_hallArmEnds_of_globalForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : aed_GlobalForestArms ω n) :
    bhs_HallArmEnds ω n := by
  classical
  obtain ⟨b, hexist, hdistinct⟩ := h
  set T := tfc_trifFinset ω n with hT
  refine ⟨b, hexist, ?_⟩
  
  refine aed_hall_of_distinctComponents T ω n T b ?_ ?_
  · 
    intro x hxT
    rw [hT, tfc_mem_trifFinset] at hxT
    obtain ⟨hbbox, _, hbinf⟩ := hexist x hxT.1 hxT.2
    exact daep_globalCutArmEnds_nonempty T ω n hn (b x) hbbox hbinf
  · 
    intro x hxT y hyT hxy
    rw [hT, tfc_mem_trifFinset] at hxT hyT
    exact hdistinct x hxT.1 hxT.2 y hyT.1 hyT.2 hxy


theorem aed_globalForestArms_of_globalCutSeparation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daep_GlobalCutSeparation ω n) :
    aed_GlobalForestArms ω n := by
  obtain ⟨b, hexist, hsep⟩ := h
  exact ⟨b, hexist, fun x hxbox htri y hybox htriy hxy =>
    hsep x hxbox htri y hybox htriy hxy⟩


theorem aed_globalCutSeparation_of_globalForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : aed_GlobalForestArms ω n) :
    daep_GlobalCutSeparation ω n := by
  obtain ⟨b, hexist, hdistinct⟩ := h
  exact ⟨b, hexist, fun x hxbox htri y hybox htriy hxy =>
    hdistinct x hxbox htri y hybox htriy hxy⟩


theorem aed_globalForestArms_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    aed_GlobalForestArms ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri _ _ _ _; exact absurd htri (hno x hxbox)


theorem aed_globalForestArms_of_disjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (b : Site d → Site d)
    (hexist : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hdistinct : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → x ≠ y →
      ¬ Connected d (removeSites (tfc_trifFinset ω n) ω) (b x) (b y)) :
    aed_GlobalForestArms ω n :=
  ⟨b, hexist, hdistinct⟩


theorem aed_globalForestArms_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    aed_GlobalForestArms ω n :=
  aed_globalForestArms_of_globalCutSeparation ω n
    (daep_globalCutSeparation_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq)


theorem aed_Tcount_le_boundary_of_globalForestArms (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : aed_GlobalForestArms ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bhs_Tcount_le_boundary_of_hall ω n (aed_hallArmEnds_of_globalForestArms ω n hn h)


theorem aed_burton_keane_bernoulli_of_globalForestArms (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → aed_GlobalForestArms ω n)
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
  bhs_burton_keane_bernoulli_of_hall hd p hp1 hp0
    (fun ω n hn => aed_hallArmEnds_of_globalForestArms ω n hn (hres ω n hn))
    htrif


end Percolation
end StatMech
