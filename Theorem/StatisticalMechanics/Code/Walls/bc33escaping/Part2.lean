/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc33escaping.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc30armforest.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc31globalarm.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc32forestsep.Part2
import Def.StatisticalMechanics.Code.Walls.bc33escaping.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc33_escapingDownArmData_of_TavoidingRayData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (h : bc33_TavoidingRayData ω n rank) :
    bc32_EscapingDownArmData ω n rank := by
  obtain ⟨b, hbdata, hsplit⟩ := h
  refine ⟨b, ?_, hsplit⟩
  intro x hxbox htri
  obtain ⟨hbbox, hbconn, r, hr0, hinj, hadj, hT⟩ := hbdata x hxbox htri
  exact ⟨hbbox, hbconn, bc33_escapingWalks_of_TavoidingRay ω n r hr0 hinj hadj hT⟩


theorem bc33_globalCutDownArmData_of_TavoidingRayData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (h : bc33_TavoidingRayData ω n rank) :
    bc30_GlobalCutDownArmData ω n rank :=
  bc32_globalCutDownArmData_of_escapingDownArmData ω n rank
    (bc33_escapingDownArmData_of_TavoidingRayData ω n rank h)


theorem bc33_bundledRootedDownArmForest_of_TavoidingRayData (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (rank : Site d → ℕ ×ₗ ℕ)
    (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y)
    (h : bc33_TavoidingRayData ω n rank) :
    bc29_BundledRootedDownArmForest ω n :=
  bc30_bundledRootedDownArmForest_of_data ω n rank hinj
    (bc33_globalCutDownArmData_of_TavoidingRayData ω n rank h)


theorem bc33_Tcount_le_boundary_of_TavoidingRayData (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) (rank : Site d → ℕ ×ₗ ℕ)
    (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y)
    (h : bc33_TavoidingRayData ω n rank) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc30_Tcount_le_boundary_of_data ω n hn rank hinj
    (bc33_globalCutDownArmData_of_TavoidingRayData ω n rank h)


theorem bc33_burton_keane_bernoulli_of_TavoidingRayData (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (rank : ConfigSpace (Sym2 (Site d)) → ℕ → Site d → ℕ ×ₗ ℕ)
    (hinj : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ),
      ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
        x ≠ y → Connected d ω x y → rank ω n x ≠ rank ω n y)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      bc33_TavoidingRayData ω n (rank ω n))
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
  bc30_burton_keane_bernoulli_of_downArmData hd p hp1 hp0
    (fun ω n hn => bc33_bundledRootedDownArmForest_of_TavoidingRayData ω n (rank ω n)
      (hinj ω n) (hres ω n hn)) htrif


theorem bc33_TavoidingRayData_of_threeChain (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g : Site d} (b : Site d → Site d)
    (hx0box : x₀ ∈ box d n) (hmbox : m ∈ box d n) (hgbox : g ∈ box d n)
    (hx0m : x₀ ≠ m) (hx0g : x₀ ≠ g) (hmg : m ≠ g)
    (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      ∃ r : ℕ → Site d, r 0 = b x₀ ∧ Function.Injective r ∧
        (∀ k, (openSubgraph d (removeSite x₀ ω)).Adj (r k) (r (k + 1))) ∧
        (∀ k, r k ∉ tfc_trifFinset ω n))
    (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧
      ∃ r : ℕ → Site d, r 0 = b m ∧ Function.Injective r ∧
        (∀ k, (openSubgraph d (removeSite m ω)).Adj (r k) (r (k + 1))) ∧
        (∀ k, r k ∉ tfc_trifFinset ω n))
    (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧
      ∃ r : ℕ → Site d, r 0 = b g ∧ Function.Injective r ∧
        (∀ k, (openSubgraph d (removeSite g ω)).Adj (r k) (r (k + 1))) ∧
        (∀ k, r k ∉ tfc_trifFinset ω n))
    (hsxm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
    (hsxg : ¬ Connected d (removeSite g ω) (b g) (b x₀))
    (hsmg : ¬ Connected d (removeSite g ω) (b g) (b m)) :
    bc33_TavoidingRayData ω n
      (fun z => if z = x₀ then toLex (0, 0)
                else if z = m then toLex (1, 0) else toLex (2, 0)) := by
  classical
  set dep : Site d → ℕ := fun z => if z = x₀ then 0 else if z = m then 1 else 2 with hdep
  have hdepx0 : dep x₀ = 0 := by simp [hdep]
  have hdepm : dep m = 1 := by simp [hdep, hx0m.symm]
  have hdepg : dep g = 2 := by simp [hdep, hx0g.symm, hmg.symm]
  have hrankeq : (fun z : Site d => if z = x₀ then toLex (0, 0)
        else if z = m then toLex (1, 0) else toLex (2, 0))
      = fun z => toLex (dep z, 0) := by
    funext z; simp only [hdep]; split_ifs <;> rfl
  rw [show (fun z : Site d => if z = x₀ then toLex (0, 0)
        else if z = m then toLex (1, 0) else toLex (2, 0))
      = fun z => toLex (dep z, 0) from hrankeq]
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    rcases hthree x hxbox htri with rfl | rfl | rfl
    · exact hbx0
    · exact hbm
    · exact hbg
  · intro x hxbox htri y hybox htriy hxy _ hlt
    rcases hthree x hxbox htri with rfl | rfl | rfl <;>
      rcases hthree y hybox htriy with rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact hsxm
    · exact hsxg
    · simp only [] at hlt; rw [hdepm, hdepx0] at hlt
      exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · exact absurd rfl hxy
    · exact hsmg
    · simp only [] at hlt; rw [hdepg, hdepx0] at hlt
      exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · simp only [] at hlt; rw [hdepg, hdepm] at hlt
      exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · exact absurd rfl hxy


theorem bc33_TavoidingRayData_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (b : Site d → Site d)
    (hx0box : x₀ ∈ box d n)
    (hydata : ∀ i, y i ∈ box d n ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      ∃ r : ℕ → Site d, r 0 = b x₀ ∧ Function.Injective r ∧
        (∀ k, (openSubgraph d (removeSite x₀ ω)).Adj (r k) (r (k + 1))) ∧
        (∀ k, r k ∉ tfc_trifFinset ω n))
    (hby : ∀ i, b (y i) ∈ box d n ∧ Connected d ω (y i) (b (y i)) ∧
      ∃ r : ℕ → Site d, r 0 = b (y i) ∧ Function.Injective r ∧
        (∀ k, (openSubgraph d (removeSite (y i) ω)).Adj (r k) (r (k + 1))) ∧
        (∀ k, r k ∉ tfc_trifFinset ω n))
    (hsx0 : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) (b x₀))
    (hssib : ∀ i j : Fin 3, (j : ℕ) < i →
      ¬ Connected d (removeSite (y i) ω) (b (y i)) (b (y j))) :
    bc33_TavoidingRayData ω n
      (fun z => if z = x₀ then toLex (0, 0)
                else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0)) := by
  classical
  set rank : Site d → ℕ ×ₗ ℕ := fun z =>
    if z = x₀ then toLex (0, 0)
    else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0) with hrank
  have hrx0 : rank x₀ = toLex (0, 0) := by simp only [hrank, if_pos rfl]
  have hry : ∀ i, rank (y i) = toLex (1, (i : ℕ)) := by
    intro i
    have hne : y i ≠ x₀ := (hydata i).2.1.symm
    have hex : ∃ k, y i = y k := ⟨i, rfl⟩
    have hchoose : hex.choose = i := hyinj hex.choose_spec.symm
    simp only [hrank, if_neg hne, dif_pos hex, hchoose]
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩
    · exact hbx0
    · exact hby i
  · intro x hxbox htri yv hyvbox htriv hxy hconn hlt
    rcases hsingle yv hyvbox htriv with rfl | ⟨i, rfl⟩
    · rcases hsingle x hxbox htri with rfl | ⟨j, rfl⟩
      · exact absurd rfl hxy
      · rw [hry j, hrx0] at hlt; exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · rcases hsingle x hxbox htri with rfl | ⟨j, rfl⟩
      · exact hsx0 i
      · rw [hry j, hry i] at hlt
        have hji : (j : ℕ) < i := by
          rw [Prod.Lex.toLex_lt_toLex] at hlt
          rcases hlt with h | ⟨_, h⟩
          · exact absurd h (lt_irrefl 1)
          · exact h
        exact hssib i j hji


theorem bc33_arc_ray :
    (fun k : ℕ => arc_p (1 + (k : ℤ))) 0 = arc_p 1 ∧
    Function.Injective (fun k : ℕ => arc_p (1 + (k : ℤ))) ∧
    (∀ k : ℕ, (openSubgraph 2 (removeSite (arc_p (-2)) arc_rayConfig)).Adj
        (arc_p (1 + (k : ℤ))) (arc_p (1 + ((k + 1 : ℕ) : ℤ)))) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro a c h
    have hz : (1 : ℤ) + (a : ℤ) = 1 + (c : ℤ) := arc_p_inj h
    have : (a : ℤ) = (c : ℤ) := by omega
    exact_mod_cast this
  · intro k
    have hcast : arc_p (1 + ((k + 1 : ℕ) : ℤ)) = arc_p (1 + (k : ℤ) + 1) := by
      norm_cast
    rw [hcast]
    exact bc32_pos_edge_open (1 + (k : ℤ)) (by omega)


theorem bc33_TavoidingRay_nonvacuous :
    ∃ (ω : ConfigSpace (Sym2 (Site 2))) (x a : Site 2) (T : Finset (Site 2)),
      a ∉ T ∧ x ∈ T ∧
      ∃ r : ℕ → Site 2, r 0 = a ∧ Function.Injective r ∧
        (∀ k, (openSubgraph 2 (removeSite x ω)).Adj (r k) (r (k + 1))) ∧
        (∀ k, r k ∉ T) := by
  classical
  obtain ⟨hr0, hinj, hadj⟩ := bc33_arc_ray
  refine ⟨arc_rayConfig, arc_p (-2), arc_p 1, {arc_p (-2)},
    ?_, ?_, fun k => arc_p (1 + (k : ℤ)), hr0, hinj, hadj, ?_⟩
  · simp only [Finset.mem_singleton]; intro h; have := arc_p_inj h; omega
  · simp
  · intro k
    simp only [Finset.mem_singleton]; intro h; have := arc_p_inj h; omega

end StatMech.Walls
