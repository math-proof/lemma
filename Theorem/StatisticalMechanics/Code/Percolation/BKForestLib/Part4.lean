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
import Def.StatisticalMechanics.Code.Percolation.BKForestLib.Part4
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem bkfl_coherentSelector_of_existsPrivateArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bkfl_ExistsPrivateArm ω n) : bkfl_CoherentArmSelector ω n := by
  classical
  
  set b : Site d → Site d := fun x =>
    if hx : x ∈ box d n ∧ IsTrifurcation d ω x then (h x hx.1 hx.2).choose else x with hb
  
  have hbval : ∀ x (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x),
      b x = (h x hxbox htri).choose := by
    intro x hxbox htri
    simp only [hb, dif_pos (⟨hxbox, htri⟩ : x ∈ box d n ∧ IsTrifurcation d ω x)]
  refine ⟨b, ?_, ?_⟩
  · 
    intro x hxbox htri
    have hspec := (h x hxbox htri).choose_spec
    rw [bkfl_ArmData, hbval x hxbox htri]
    exact hspec.1
  · 
    intro x hxbox htri y hybox htriy hxy hconn
    have hspecx := (h x hxbox htri).choose_spec
    have hspecy := (h y hybox htriy).choose_spec
    have hyT : y ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
    have hxT : x ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
    refine ⟨?_, ?_⟩
    · 
      rw [bkfl_inArm, hbval x hxbox htri]
      exact hspecx.2.1 y hyT (Ne.symm hxy)
    · 
      rw [hbval y hybox htriy]
      exact hspecy.2.2 x hxT hxy


theorem bkfl_privateArm_of_existsPrivateArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bkfl_ExistsPrivateArm ω n) : daepf_PrivateArm ω n :=
  bkfl_privateArm_of_coherentSelector ω n (bkfl_coherentSelector_of_existsPrivateArm ω n h)


theorem bkfl_Tcount_le_boundary_of_existsPrivateArm (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) (h : bkfl_ExistsPrivateArm ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bkfl_Tcount_le_boundary_of_coherentSelector ω n hn
    (bkfl_coherentSelector_of_existsPrivateArm ω n h)


theorem bkfl_trif_branches (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (htri : IsTrifurcation d ω x) :
    ∃ a₁ a₂ a₃ : Site d,
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      (Connected d ω x a₁ ∧ Connected d ω x a₂ ∧ Connected d ω x a₃) ∧
      (¬ Connected d (removeSite x ω) a₁ a₂ ∧ ¬ Connected d (removeSite x ω) a₁ a₃ ∧
        ¬ Connected d (removeSite x ω) a₂ a₃) := by
  obtain ⟨a₁, a₂, a₃, hne, hconn, _, hsep⟩ := htri
  exact ⟨a₁, a₂, a₃, hne, hconn, hsep⟩


theorem bkfl_vertex_meets_atMostOne_arm (ω : ConfigSpace (Sym2 (Site d)))
    {x a₁ a₂ a₃ v : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
    (bkfl_inArm ω x a₁ v → ¬ bkfl_inArm ω x a₂ v ∧ ¬ bkfl_inArm ω x a₃ v) ∧
    (bkfl_inArm ω x a₂ v → ¬ bkfl_inArm ω x a₁ v ∧ ¬ bkfl_inArm ω x a₃ v) ∧
    (bkfl_inArm ω x a₃ v → ¬ bkfl_inArm ω x a₁ v ∧ ¬ bkfl_inArm ω x a₂ v) := by
  obtain ⟨n12, n13, n23⟩ := bkfl_atMostOneArm ω hd12 hd13 hd23 (v := v)
  exact ⟨fun h1 => ⟨fun h2 => n12 ⟨h1, h2⟩, fun h3 => n13 ⟨h1, h3⟩⟩,
    fun h2 => ⟨fun h1 => n12 ⟨h1, h2⟩, fun h3 => n23 ⟨h2, h3⟩⟩,
    fun h3 => ⟨fun h1 => n13 ⟨h1, h3⟩, fun h2 => n23 ⟨h2, h3⟩⟩⟩


theorem bkfl_pointwise_of_freeArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (T : Finset (Site d)) {x a : Site d}
    (hdata : a ∈ box d n ∧ Connected d ω x a ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) a).Infinite)
    (hfree : ∀ y ∈ T, y ≠ x → ¬ Connected d (removeSite x ω) a y)
    (hfar : ∀ z ∈ T, z ≠ x → Connected d (removeSite z ω) a x) :
    bkfl_PointwisePrivateFar ω n T x a :=
  ⟨hdata, hfree, hfar⟩


end Percolation
end StatMech
