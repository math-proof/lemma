/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc31surgery.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc32surgery
import Theorem.StatisticalMechanics.Code.Ising.BackboneResummation.Part2
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Ising.HdomMultiplicity.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Def.StatisticalMechanics.Code.Walls.gc33witness
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc33_J_nonneg : ∀ e, 0 ≤ gc33_J e := by
  intro e; unfold gc33_J; split <;> norm_num


theorem gc33_ma_01 : ∀ e ∈ gc33_G.edgeFinset, gc33_ma e ≤ 1 := by
  intro e _; unfold gc33_ma; split <;> omega


theorem gc33_ma_sources : Sharpness.sources gc33_G gc33_ma = (∅ : Finset (Fin 5)) := by
  ext z
  simp only [Sharpness.mem_sources]
  refine ⟨fun h => ?_, fun h => absurd h (Finset.notMem_empty z)⟩
  exfalso; revert h
  fin_cases z <;> · unfold Sharpness.incidentFlux gc33_ma gc33_G; decide


theorem gc33_mstar_sources : Sharpness.sources gc33_G gc33_mstar = (∅ : Finset (Fin 5)) := by
  ext z
  simp only [Sharpness.mem_sources]
  refine ⟨fun h => ?_, fun h => absurd h (Finset.notMem_empty z)⟩
  exfalso; revert h
  fin_cases z <;> · unfold Sharpness.incidentFlux gc33_mstar gc33_G; decide


theorem gc33_ma_conn (a b : Fin 5) (hab : a ≠ b) (he : gc33_ma s(a, b) = 1) :
    connP (oddEdges gc33_G.edgeFinset gc33_ma) a b := by
  apply Relation.ReflTransGen.single
  refine ⟨s(a, b), ?_, Sym2.mem_mk_left a b, Sym2.mem_mk_right a b, hab⟩
  rw [oddEdges, Finset.mem_filter]
  exact ⟨by rw [SimpleGraph.mem_edgeFinset]; exact hab, by rw [he]; exact ⟨0, rfl⟩⟩


theorem gc33_ma_allConn : hnw_allConn gc33_G gc33_ma 0 1 2 :=
  ⟨gc33_ma_conn 1 2 (by decide) (by unfold gc33_ma; decide),
   gc33_ma_conn 0 2 (by decide) (by unfold gc33_ma; decide),
   gc33_ma_conn 0 1 (by decide) (by unfold gc33_ma; decide)⟩


theorem gc33_mstar_posEdges : posEdges gc33_G.edgeFinset gc33_mstar = {s(3, 4)} := by
  unfold posEdges gc33_mstar; decide


theorem gc33_mstar_noneConn : hnw_noneConn gc33_G gc33_mstar 0 1 2 := by
  rw [hnw_noneConn, gc33_mstar_posEdges]
  refine ⟨?_, ?_, ?_⟩
  · exact fun h => absurd (gc33_connP_isolated (a := (1 : Fin 5)) (by decide) h) (by decide)
  · exact fun h => absurd (gc33_connP_isolated (a := (0 : Fin 5)) (by decide) h) (by decide)
  · exact fun h => absurd (gc33_connP_isolated (a := (0 : Fin 5)) (by decide) h) (by decide)


theorem gc33_weight_ma : Sharpness.weight gc33_G 1 gc33_J gc33_ma = 1 := by
  unfold Sharpness.weight
  rw [Finset.prod_eq_one]
  intro e he
  have hma : gc33_ma e = 0 ∨ gc33_ma e = 1 := by unfold gc33_ma; split <;> simp
  have hJ : gc33_J e = 1 ∨ (gc33_J e = 8 ∧ gc33_ma e = 0) := by
    unfold gc33_J gc33_ma
    by_cases h34 : e = s(3, 4)
    · exact Or.inr ⟨by rw [if_pos h34], by rw [if_neg]; subst h34; decide⟩
    · exact Or.inl (by rw [if_neg h34])
  rcases hma with h0 | h1
  · rw [h0]; simp
  · rcases hJ with hJ1 | ⟨_, hJ0⟩
    · rw [h1, hJ1]; norm_num
    · rw [h1] at hJ0; simp at hJ0


theorem gc33_weight_mstar : Sharpness.weight gc33_G 1 gc33_J gc33_mstar = 32 := by
  unfold Sharpness.weight
  rw [Finset.prod_eq_single_of_mem s(3, 4) (by decide)]
  · unfold gc33_mstar gc33_J; norm_num
  · intro e _ hne
    unfold gc33_mstar gc33_J
    rw [if_neg hne, if_neg hne]; norm_num


theorem gc33_mass_ma_le : hnw_mass gc33_G 1 gc33_J gc33_ma ∅ ≤ 8 := by
  have hcard : (Fintype.card {K : Sharpness.Current (Fin 5) // ∀ e, K e ≤ gc33_ma e} : ℝ) = 8 := by
    rw [gc33_split_card gc33_ma]
    rw [show (∏ e : Sym2 (Fin 5), (gc33_ma e + 1)) = 8 from by unfold gc33_ma; decide]
    norm_num
  have := gc33_mass_le gc33_G 1 gc33_J (by norm_num) gc33_J_nonneg gc33_ma gc33_ma_01 ∅
  rw [hcard, gc33_weight_ma] at this
  linarith


theorem gc33_mass_ma_pos : 0 < hnw_mass gc33_G 1 gc33_J gc33_ma ∅ := by
  have hge := hmu_mass_ge_weight gc33_G 1 gc33_J (by norm_num) gc33_J_nonneg gc33_ma
  rw [gc33_ma_sources, gc33_weight_ma] at hge
  linarith


theorem gc33_mass_mstar_ge : 32 ≤ hnw_mass gc33_G 1 gc33_J gc33_mstar ∅ := by
  have hge := hmu_mass_ge_weight gc33_G 1 gc33_J (by norm_num) gc33_J_nonneg gc33_mstar
  rw [gc33_mstar_sources, gc33_weight_mstar] at hge
  linarith


theorem gc33_doubling : 2 * hnw_mass gc33_G 1 gc33_J gc33_ma ∅
    ≤ hnw_mass gc33_G 1 gc33_J gc33_mstar ∅ := by
  have h1 := gc33_mass_ma_le
  have h2 := gc33_mass_mstar_ge
  linarith


theorem gc33_ma_ne_mstar : gc33_ma ≠ gc33_mstar := by
  intro h
  have := congrFun h s(0, 1)
  unfold gc33_ma gc33_mstar at this
  revert this; decide


theorem gc33_allFilter : bbr_allFilter gc33_G gc33_M 0 1 2 = {gc33_ma} := by
  unfold bbr_allFilter gc33_M
  ext m
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hmem, hall⟩
    rcases hmem with rfl | rfl
    · rfl
    · exact absurd hall (hnw_noneConn_not_allConn gc33_G gc33_mstar gc33_mstar_noneConn)
  · rintro rfl; exact ⟨Or.inl rfl, gc33_ma_allConn⟩


theorem gc33_mstar_in_noneFilter : gc33_mstar ∈ bbr_noneFilter gc33_G gc33_M 0 1 2 := by
  unfold bbr_noneFilter gc33_M
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), gc33_mstar_noneConn⟩


theorem gc33_massDoubling_witness :
    gc31_MassDoublingSurgery gc33_G 1 gc33_J gc33_M ∅ 0 1 2 :=
  gc31_massDoubling_of_singleton_dominated gc33_G 1 gc33_J gc33_M ∅ 0 1 2
    gc33_ma gc33_mstar gc33_allFilter gc33_mstar_in_noneFilter gc33_doubling


theorem gc33_backboneSurgery_witness :
    bbr_BackboneSurgery gc33_G 1 gc33_J gc33_M ∅ 0 1 2 :=
  gc31_backboneSurgery_of_massDoubling gc33_G 1 gc33_J gc33_M ∅ 0 1 2 gc33_massDoubling_witness


theorem gc33_witness_positive_masses :
    0 < hnw_mass gc33_G 1 gc33_J gc33_ma ∅
      ∧ 0 < hnw_mass gc33_G 1 gc33_J gc33_mstar ∅
      ∧ 0 < 2 * hnw_mass gc33_G 1 gc33_J gc33_ma ∅
      ∧ 2 * hnw_mass gc33_G 1 gc33_J gc33_ma ∅ ≤ hnw_mass gc33_G 1 gc33_J gc33_mstar ∅ := by
  refine ⟨gc33_mass_ma_pos, ?_, ?_, gc33_doubling⟩
  · have := gc33_mass_mstar_ge; linarith
  · have := gc33_mass_ma_pos; linarith


theorem gc33_massDoubling_of_injection {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ) (J : Sym2 V → ℝ)
    (M : Finset (Sharpness.Current V)) (B : Finset V) (o x y : V)
    (Φ : Sharpness.Current V → Sharpness.Current V)
    (hmem : ∀ m ∈ bbr_allFilter G M o x y, Φ m ∈ bbr_noneFilter G M o x y)
    (hinj : Set.InjOn Φ (bbr_allFilter G M o x y))
    (hdoub : ∀ m ∈ bbr_allFilter G M o x y, 2 * hnw_mass G β J m B ≤ hnw_mass G β J (Φ m) B) :
    gc31_MassDoublingSurgery G β J M B o x y :=
  ⟨Φ, hmem, hinj, hdoub⟩


theorem gc33_surgery_unsat_of_zero_targets {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Sharpness.Current V)) (B : Finset V) (o x y : V)
    (ma : Sharpness.Current V) (hma : ma ∈ bbr_allFilter G M o x y)
    (hpos : 0 < hnw_mass G β J ma B)
    (hzero : ∀ m' ∈ bbr_noneFilter G M o x y, hnw_mass G β J m' B = 0) :
    ¬ gc31_MassDoublingSurgery G β J M B o x y :=
  gc32_massDoubling_unsat_of_zero_targets G β J hβ hJ M B o x y ma hma hpos hzero


theorem gc33_mass_summand_cut_factor {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ) (J : Sym2 V → ℝ)
    (m K : Sharpness.Current V) (p : Sym2 V → Prop) [DecidablePred p] :
    Sharpness.weight G β J K * Sharpness.weight G β J (fun e => m e - K e)
      = (Sharpness.weight G β J (StatMech.Ising.restrictCut K p)
          * Sharpness.weight G β J (StatMech.Ising.restrictCut (fun e => m e - K e) p))
        * (Sharpness.weight G β J (StatMech.Ising.restrictCut K (fun e => ¬ p e))
          * Sharpness.weight G β J (StatMech.Ising.restrictCut (fun e => m e - K e)
              (fun e => ¬ p e))) :=
  gc32_split_weight_cut_factor G β J m K p


end StatMech.Walls
