/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Theorem.StatisticalMechanics.Code.FK.CenteredFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Def.StatisticalMechanics.Code.FK.EdgeConfigZ.Part16
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


section Convergence

variable {d : ℕ}


theorem ecz_blockOscillation_satisfiable :
    ∃ (g : ℕ → ℝ) (bj : ℕ → ℕ) (osc : ℕ → ℝ), Tendsto bj atTop atTop ∧ Tendsto osc atTop (𝓝 0)
      ∧ (∀ n, |g n - g (agl_K (bj n))| ≤ osc (bj n)) := by
  refine ⟨fun _ => 0, agl_K, fun _ => 0, agl_K_tendsto_atTop, tendsto_const_nhds, ?_⟩
  intro n; simp


theorem ecz_blockOscillation_of_perEdgeDensity (s : ℝ)
    (hρ : ecz_PerEdgeDensityConverges d s) : ecz_BlockOscillation d s := by
  classical
  obtain ⟨ρ, hρ⟩ := hρ
  set B := Real.log (1 + Real.exp s) with hB
  have hg : Tendsto (fun n => ecz_edgeFreeEnergy d s n) atTop (𝓝 (B - ρ)) := by
    have h1 : Tendsto (fun n => -(ecz_u d s n / ((boxGraph d n).edgeFinset.card : ℝ)) + B)
        atTop (𝓝 (-ρ + B)) := (hρ.neg).add_const B
    have heq : (fun n => ecz_edgeFreeEnergy d s n)
        = (fun n => -(ecz_u d s n / ((boxGraph d n).edgeFinset.card : ℝ)) + B) := by
      funext n; rw [ecz_edgeFreeEnergy]
    rw [heq]; convert h1 using 2; ring
  have hgK : Tendsto (fun m => ecz_edgeFreeEnergy d s (agl_K m)) atTop (𝓝 (B - ρ)) :=
    hg.comp agl_K_tendsto_atTop
  refine ⟨id, fun m => |ecz_edgeFreeEnergy d s m - (B - ρ)|
      + |ecz_edgeFreeEnergy d s (agl_K m) - (B - ρ)|, tendsto_id, ?_, ?_⟩
  · have h1 : Tendsto (fun m => |ecz_edgeFreeEnergy d s m - (B - ρ)|) atTop (𝓝 0) := by
      have := (hg.sub_const (B - ρ)).abs; simpa using this
    have h2 : Tendsto (fun m => |ecz_edgeFreeEnergy d s (agl_K m) - (B - ρ)|) atTop (𝓝 0) := by
      have := (hgK.sub_const (B - ρ)).abs; simpa using this
    simpa using h1.add h2
  · intro n
    simp only [id]
    calc |ecz_edgeFreeEnergy d s n - ecz_edgeFreeEnergy d s (agl_K n)|
        = |(ecz_edgeFreeEnergy d s n - (B - ρ)) - (ecz_edgeFreeEnergy d s (agl_K n) - (B - ρ))| := by
            ring_nf
      _ ≤ |ecz_edgeFreeEnergy d s n - (B - ρ)| + |ecz_edgeFreeEnergy d s (agl_K n) - (B - ρ)| :=
            abs_sub _ _


theorem ecz_edgeFE_tendsto (hd : 1 ≤ d) (s : ℝ)
    (hbox : ∀ j, 0 < (boxGraph d (agl_K j)).edgeFinset.card)
    (hosc : ecz_BlockOscillation d s) :
    ∃ L : ℝ, Tendsto (fun n => ecz_edgeFreeEnergy d s n) atTop (𝓝 L) := by
  classical
  obtain ⟨I, hInn, hIsum, hudbl, hEdge⟩ := ecz_additiveDoublingBound d hd s
  obtain ⟨bj, osc, hbj, hosc0, hsand⟩ := hosc
  set c : ℝ := -Real.log (1 - fsc_logistic s) with hc
  have hp1 : fsc_logistic s < 1 := fsc_logistic_lt_one s
  have hp0 : (0:ℝ) < fsc_logistic s := fsc_logistic_pos s
  have hc0 : 0 ≤ c := by
    rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  have hEpos : ∀ j, 0 < agl_E d (agl_K j) := fun j => by
    unfold agl_E; exact_mod_cast hbox j
  
  
  
  set M : ℝ := 3 * Real.log 2 + c with hM
  have hMc0 : 0 ≤ M + c := by
    rw [hM]; have hl2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num); linarith
  have hIE0 : ∀ j, 0 ≤ I j / agl_E d (agl_K (j + 1)) := fun j =>
    div_nonneg (hInn j) (hEpos (j + 1)).le
  set δ : ℕ → ℝ := fun j => (M + c) * (I j / agl_E d (agl_K (j + 1))) with hδ
  apply agl_perVolume_converges
    (fun n => ecz_edgeFreeEnergy d s n) agl_K δ osc bj
  · intro j; exact mul_nonneg hMc0 (hIE0 j)
  · exact hIsum.mul_left (M + c)
  · 
    intro j
    rw [ecz_edgeFE_eq s (agl_K j), ecz_edgeFE_eq s (agl_K (j + 1))]
    have hstep := bxt_perVolume_doubling_step (a := ecz_u d s (agl_K j))
      (A := ecz_u d s (agl_K (j + 1))) (e := agl_E d (agl_K j)) (E := agl_E d (agl_K (j + 1)))
      (K := (2 : ℝ) ^ d) (c := c) (i := I j)
      (hEpos j) (hEpos (j + 1)) hc0 (hInn j) (hudbl j) (hEdge j)
    
    have hl2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hle1 : (1:ℝ) ≤ 1 + Real.exp s := by have := Real.exp_pos s; linarith
    have hlog1 : (0:ℝ) ≤ Real.log (1 + Real.exp s) := Real.log_nonneg hle1
    
    have hupper : -(ecz_u d s (agl_K j) / agl_E d (agl_K j)) ≤ 3 * Real.log 2 := by
      have h := ecz_edgeFE_le_const d (agl_K j) hd (agl_K_pos j) s (hbox j)
      rw [ecz_edgeFE_eq] at h; linarith
    
    have hlower : ecz_u d s (agl_K j) / agl_E d (agl_K j) ≤ c := by
      have hEr : (0:ℝ) < agl_E d (agl_K j) := hEpos j
      have hge := ecz_neglogZEdge_le_edges (boxGraph d (agl_K j)) hp0 hp1 (by norm_num : (1:ℝ) ≤ 2)
      
      rw [div_le_iff₀ hEr]
      show ecz_u d s (agl_K j) ≤ c * agl_E d (agl_K j)
      have : ecz_u d s (agl_K j) ≤ agl_E d (agl_K j) * c := by
        simpa [ecz_u, agl_E, hc] using hge
      linarith [mul_comm (agl_E d (agl_K j)) c, this]
    have huEbd : |ecz_u d s (agl_K j)| / agl_E d (agl_K j) ≤ M := by
      have hquot : |ecz_u d s (agl_K j)| / agl_E d (agl_K j)
          = |ecz_u d s (agl_K j) / agl_E d (agl_K j)| := by
        rw [abs_div, abs_of_pos (hEpos j)]
      rw [hquot, abs_le]
      refine ⟨?_, ?_⟩
      · rw [hM]; linarith [hupper, hc0]
      · rw [hM]; linarith [hlower, hl2]
    have hdefle : (|ecz_u d s (agl_K j)| / agl_E d (agl_K j) + c)
        * (I j / agl_E d (agl_K (j + 1))) ≤ δ j := by
      show _ ≤ (M + c) * (I j / agl_E d (agl_K (j + 1)))
      apply mul_le_mul_of_nonneg_right _ (hIE0 j)
      linarith [huEbd]
    have hgoal : -(ecz_u d s (agl_K j) / agl_E d (agl_K j)) - δ j
        ≤ -(ecz_u d s (agl_K (j + 1)) / agl_E d (agl_K (j + 1))) := by linarith [hstep, hdefle]
    linarith
  · 
    refine ⟨3 * Real.log 2 + Real.log (1 + Real.exp s), ?_⟩
    rintro x ⟨j, rfl⟩
    simp only
    exact ecz_edgeFE_le_const d (agl_K j) hd (agl_K_pos j) s (hbox j)
  · exact hbj
  · exact hosc0
  · exact hsand


theorem ecz_cfe_centered_tendsto (hd : 1 ≤ d) (t : ℝ)
    (hbox : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    (hosct : ecz_BlockOscillation d t) (hosc0 : ecz_BlockOscillation d 0) :
    ∃ G : ℝ, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 G) := by
  obtain ⟨Lt, hLt⟩ := ecz_edgeFE_tendsto hd t (fun j => ecz_box_edge_pos d hd (agl_K_pos j)) hosct
  obtain ⟨L0, hL0⟩ := ecz_edgeFE_tendsto hd 0 (fun j => ecz_box_edge_pos d hd (agl_K_pos j)) hosc0
  refine ⟨Lt - L0, ?_⟩
  
  
  refine Tendsto.congr' ?_ (hLt.sub hL0)
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (ecz_centered_eq_cfe t n (hbox n hn)).symm


theorem ecz_centeredConvergence (hd : 1 ≤ d)
    (hbox : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    (hosc : ∀ s, ecz_BlockOscillation d s) :
    ∃ G : ℝ → ℝ,
      (∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
        ∧ ConvexOn ℝ Set.univ G ∧ G 0 = 0 := by
  classical
  have hconv : ∀ t, ∃ G : ℝ,
      Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 G) :=
    fun t => ecz_cfe_centered_tendsto hd t hbox (hosc t) (hosc 0)
  refine ⟨fun t => (hconv t).choose, fun t => (hconv t).choose_spec, ?_, ?_⟩
  · 
    
    
    refine ivp2_convexOn_of_tendsto (l := (atTop : Filter ℕ))
      (fun n => cfe_centered (boxGraph d (n + 1)) 2) _
      (fun n => cfe_centered_convexOn (boxGraph d (n + 1)) 2 (by norm_num)
        (hbox (n + 1) (by omega))) ?_
    intro t
    exact ((hconv t).choose_spec).comp (tendsto_add_atTop_nat 1)
  · 
    show (hconv 0).choose = 0
    have h0 : Tendsto (fun n => cfe_centered (boxGraph d n) 2 0) atTop (𝓝 ((hconv 0).choose)) :=
      (hconv 0).choose_spec
    have hzero : Tendsto (fun n => cfe_centered (boxGraph d n) 2 0) atTop (𝓝 0) := by
      simp only [cfe_centered_zero]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h0 hzero


theorem ecz_fk_uniqueness_of_blockOscillation (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hEbox : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    (hosc : ∀ s, ecz_BlockOscillation d s) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
  obtain ⟨G, hboxfree, hG, _hG0⟩ := ecz_centeredConvergence hd hEbox hosc
  exact ecz_fk_uniqueness_of_centeredData_n1 hd N eb heb hEbox hG hboxfree


theorem ecz_fk_uniqueness_of_perEdgeDensity (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hEbox : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    (hρ : ∀ s, ecz_PerEdgeDensityConverges d s) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  ecz_fk_uniqueness_of_blockOscillation hd N eb heb hEbox
    (fun s => ecz_blockOscillation_of_perEdgeDensity s (hρ s))


theorem ecz_fk_uniqueness (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  ecz_fk_uniqueness_of_perEdgeDensity hd N eb heb
    (fun n hn => ecz_box_edge_pos d hd hn)
    (fun s => ecz_perEdgeDensityConverges hd s (fun n hn => ecz_box_edge_pos d hd hn))


example : True := by
  have hne : (boxGraph 2 1).edgeFinset.Nonempty :=
    Finset.card_pos.mp (ecz_box_edge_pos 2 (by norm_num) (by norm_num))
  obtain ⟨eb, heb⟩ := hne
  have _ := ecz_fk_uniqueness (d := 2) (by norm_num) (N := 1) eb heb
  trivial

end Convergence


theorem ecz_residue_remark : True := trivial

end FK
end StatMech
