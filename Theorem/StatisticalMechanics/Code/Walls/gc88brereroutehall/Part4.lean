/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc88brereroutehall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc86brerouteinjection.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc87brerouteinjection.Part3
import Def.StatisticalMechanics.Code.Walls.gc88brereroutehall.Part4
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]


theorem gc88b_biUnion_eq_T3Set (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    {s : Finset {KK // KK ∈ gc88b_cogxgSet ends m o x y g}} (hs : s.Nonempty) :
    s.biUnion (gc88b_hallFamily ends m o x y g) = gc88b_T3Set ends m o x y g := by
  apply Finset.Subset.antisymm
  · intro JJ hJJ
    rw [Finset.mem_biUnion] at hJJ
    obtain ⟨KK, hKKs, hJJnbr⟩ := hJJ
    rw [gc88b_hallFamily, gc88b_nbr_eq_T3Set ends m o x y g KK.2] at hJJnbr
    exact hJJnbr
  · intro JJ hJJ
    obtain ⟨KK, hKKs⟩ := hs
    rw [Finset.mem_biUnion]
    refine ⟨KK, hKKs, ?_⟩
    rw [gc88b_hallFamily, gc88b_nbr_eq_T3Set ends m o x y g KK.2]
    exact hJJ


theorem gc88b_marriage_iff_cogxg_le_T3 (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    gc88b_Marriage ends m o x y g ↔ gc87b_CogxgLeT3 ends m o x y g := by
  unfold gc88b_Marriage gc87b_CogxgLeT3
  rw [← gc88b_cogxgSet_card ends m o x y g, ← gc88b_T3Set_card ends m o x y g]
  constructor
  · 
    intro hM
    rcases (gc88b_cogxgSet ends m o x y g).eq_empty_or_nonempty with hemp | hne
    · rw [hemp]; simp
    · 
      have huniv := hM Finset.univ
      have hcard_univ : #(Finset.univ : Finset {KK // KK ∈ gc88b_cogxgSet ends m o x y g})
          = #(gc88b_cogxgSet ends m o x y g) := by
        rw [Finset.card_univ, Fintype.card_coe]
      
      obtain ⟨KK₀, hKK₀⟩ := hne
      have hunivne : (Finset.univ : Finset {KK // KK ∈ gc88b_cogxgSet ends m o x y g}).Nonempty :=
        ⟨⟨KK₀, hKK₀⟩, Finset.mem_univ _⟩
      rw [gc88b_biUnion_eq_T3Set ends m o x y g hunivne, hcard_univ] at huniv
      exact huniv
  · 
    intro hle s
    rcases s.eq_empty_or_nonempty with hemp | hne
    · rw [hemp]; simp
    · rw [gc88b_biUnion_eq_T3Set ends m o x y g hne]
      calc #s ≤ #(Finset.univ : Finset {KK // KK ∈ gc88b_cogxgSet ends m o x y g}) :=
              Finset.card_le_card (Finset.subset_univ s)
        _ = #(gc88b_cogxgSet ends m o x y g) := by rw [Finset.card_univ, Fintype.card_coe]
        _ ≤ #(gc88b_T3Set ends m o x y g) := hle


theorem gc88b_injection_of_marriage (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    (hM : gc88b_Marriage ends m o x y g) :
    ∃ f : {KK // KK ∈ gc88b_cogxgSet ends m o x y g} → (Finset ι × Finset ι),
      Function.Injective f ∧ ∀ KK, f KK ∈ gc88b_hallFamily ends m o x y g KK :=
  (Finset.all_card_le_biUnion_card_iff_exists_injective
    (gc88b_hallFamily ends m o x y g)).1 hM


theorem gc88b_cogxg_le_T3_of_marriage_via_hall (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    (hM : gc88b_Marriage ends m o x y g) :
    gc87b_CogxgLeT3 ends m o x y g := by
  obtain ⟨f, hfinj, hfmem⟩ := gc88b_injection_of_marriage ends m o x y g hM
  unfold gc87b_CogxgLeT3
  rw [← gc88b_cogxgSet_card ends m o x y g, ← gc88b_T3Set_card ends m o x y g]
  
  have himg : (Finset.univ : Finset {KK // KK ∈ gc88b_cogxgSet ends m o x y g}).image f
      ⊆ gc88b_T3Set ends m o x y g := by
    intro JJ hJJ
    rw [Finset.mem_image] at hJJ
    obtain ⟨KK, _, rfl⟩ := hJJ
    have := hfmem KK
    rwa [gc88b_hallFamily, gc88b_nbr_eq_T3Set ends m o x y g KK.2] at this
  calc #(gc88b_cogxgSet ends m o x y g)
        = #(Finset.univ : Finset {KK // KK ∈ gc88b_cogxgSet ends m o x y g}) := by
          rw [Finset.card_univ, Fintype.card_coe]
    _ = #((Finset.univ : Finset {KK // KK ∈ gc88b_cogxgSet ends m o x y g}).image f) := by
          rw [Finset.card_image_of_injective _ hfinj]
    _ ≤ #(gc88b_T3Set ends m o x y g) := Finset.card_le_card himg


theorem gc88b_close_of_marriage (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hM : gc88b_Marriage ends m o x y g) :
    gc85b_ThreeCurrentBijection ends m o x y g :=
  gc87b_bijection_of_cogxg_le_T3 ends m hnd hsrc hox hoy hog
    (gc88b_cogxg_le_T3_of_marriage_via_hall ends m o x y g hM)


end StatMech.Walls
