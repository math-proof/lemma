/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc26forest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsFinal.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc24coarsetrif.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc25renormcount
import Def.StatisticalMechanics.Code.Walls.bc26forest.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc26_privateFarOrder_iff_coherentSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc26_PrivateFarOrder ω n ↔ bkfl_CoherentArmSelector ω n := Iff.rfl


theorem bc26_privateArm_of_privateFarOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc26_PrivateFarOrder ω n) : daepf_PrivateArm ω n :=
  bkfl_privateArm_of_coherentSelector ω n h


theorem bc26_count_of_privateFarOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : bc26_PrivateFarOrder ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daepf_Tcount_le_boundary_of_privateArm ω n hn
    (bc26_privateArm_of_privateFarOrder ω n h)


theorem bc26_burton_keane_bernoulli_of_privateFarOrder (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc26_PrivateFarOrder ω n)
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
  daepf_burton_keane_bernoulli_of_privateArm hd p hp1 hp0
    (fun ω n hn => bc26_privateArm_of_privateFarOrder ω n (hres ω n hn)) htrif


theorem bc26_coarseTrif_arms_cutInfinite {ω : ConfigSpace (Sym2 (Site d))}
    (h : IsCoarseTrifurcation d 0 ω) :
    ∃ a₁ a₂ a₃ : Site d,
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      (Connected d ω (0 : Site d) a₁ ∧ Connected d ω (0 : Site d) a₂ ∧
        Connected d ω (0 : Site d) a₃) ∧
      ((cluster d (removeSite (0 : Site d) ω) a₁).Infinite ∧
        (cluster d (removeSite (0 : Site d) ω) a₂).Infinite ∧
        (cluster d (removeSite (0 : Site d) ω) a₃).Infinite) ∧
      (¬ Connected d (removeSite (0 : Site d) ω) a₁ a₂ ∧
        ¬ Connected d (removeSite (0 : Site d) ω) a₁ a₃ ∧
        ¬ Connected d (removeSite (0 : Site d) ω) a₂ a₃) := by
  obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, hne, hbox, _hadj, hconn, hinf, hsep⟩ := h
  have hbox0 : ∀ {b : Site d}, b ∈ box d 0 → b = (0 : Site d) := by
    intro b hb; rw [bc24_box_zero] at hb; simpa using hb
  have hb₁0 : b₁ = (0 : Site d) := hbox0 hbox.1
  have hb₂0 : b₂ = (0 : Site d) := hbox0 hbox.2.1
  have hb₃0 : b₃ = (0 : Site d) := hbox0 hbox.2.2
  have hbridge := bc24_removeSites_box_zero (d := d) ω
  rw [hbridge] at hinf hsep
  refine ⟨a₁, a₂, a₃, hne, ?_, hinf, hsep⟩
  exact ⟨(hb₁0 ▸ hconn.1).symm, (hb₂0 ▸ hconn.2.1).symm, (hb₃0 ▸ hconn.2.2).symm⟩


theorem bc26_globalForestArms_of_uniqueTrif_cutArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    aed_GlobalForestArms ω n :=
  aed_globalForestArms_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq


theorem bc26_privateFarOrder_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc26_PrivateFarOrder ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri _ _ _ _ _; exact absurd htri (hno x hxbox)


theorem bc26_privateFarOrder_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    bc26_PrivateFarOrder ω n := by
  classical
  
  have hT : tfc_trifFinset ω n = {x₀} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩, ?_⟩
    intro y hy; rw [tfc_mem_trifFinset] at hy; exact huniq y hy.1 hy.2
  have hcut : removeSites (tfc_trifFinset ω n) ω = removeSite x₀ ω := by
    rw [hT, daep_removeSites_singleton]
  refine ⟨fun _ => a, ?_, ?_⟩
  · intro x hxbox htri
    have hx0 : x = x₀ := huniq x hxbox htri
    subst hx0
    refine ⟨habox, haconn, ?_⟩
    rw [hcut]; exact hainf
  · intro x hxbox htri y hybox htriy hxy _
    exact absurd ((huniq x hxbox htri).trans (huniq y hybox htriy).symm) hxy


theorem bc26_privateFarOrder_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d)
    (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hdata_x : bkfl_ArmData ω n b x₀) (hdata_y : bkfl_ArmData ω n b y₀)
    (hpf_xy : bkfl_PrivateFar ω b x₀ y₀) (hpf_yx : bkfl_PrivateFar ω b y₀ x₀) :
    bc26_PrivateFarOrder ω n := by
  classical
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hdata_x
    · exact hdata_y
  · intro x hxbox htri y hybox htriy hxy _
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · exact hpf_xy
    · rcases htwo y hybox htriy with rfl | rfl
      · exact hpf_yx
      · exact absurd rfl hxy

end StatMech.Walls
