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
import Def.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
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


section BoxNesting

variable {d : ℕ}


section VanHove

variable {d : ℕ}


theorem ecz_g_dyadic_tendsto (s : ℝ) (L : ℝ)
    (hL : Tendsto (fun j => ecz_f d s (agl_K j)) atTop (𝓝 L)) :
    Tendsto (fun j => ecz_g d s (agl_K j)) atTop (𝓝 L) := by
  set c := -Real.log (1 - fsc_logistic s) with hc
  
  have hKtop : Tendsto (fun j => (2 * ((agl_K j : ℕ) : ℝ) + 1)) atTop atTop :=
    ecz_denom_tendsto_atTop.comp (by exact_mod_cast agl_K_tendsto_atTop)
  have h0 : Tendsto (fun j => (1 : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := (1:ℝ))).div_atTop hKtop
  have hR : Tendsto (fun j => 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)) atTop (𝓝 1) := by
    have heq : ∀ j, 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)
        = 1 - 1 / (2 * ((agl_K j : ℕ) : ℝ) + 1) := by
      intro j
      have hpos : (0:ℝ) < 2 * ((agl_K j : ℕ) : ℝ) + 1 := by positivity
      field_simp; ring
    rw [show (fun j => 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1))
        = (fun j => 1 - 1 / (2 * ((agl_K j : ℕ) : ℝ) + 1)) from funext heq]
    have := h0.const_sub (1 : ℝ); simpa using this
  have hprod : Tendsto (fun j => ecz_g d s (agl_K j)) atTop
      (𝓝 ((1 : ℝ) * L + (1 - 1) * c)) := by
    have heq : (fun j => ecz_g d s (agl_K j))
        = (fun j => (2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)) * ecz_f d s (agl_K j)
          + (1 - 2 * ((agl_K j : ℕ) : ℝ) / (2 * ((agl_K j : ℕ) : ℝ) + 1)) * c) := by
      funext j; rw [ecz_g, hc]
    rw [heq]
    exact ((hR.mul hL).add ((tendsto_const_nhds.sub hR).mul tendsto_const_nhds))
  rw [show (1 : ℝ) * L + (1 - 1) * c = L by ring] at hprod
  exact hprod


theorem ecz_upperSeq_tendsto (hd : 1 ≤ d) (s : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun n =>
        (((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * ecz_f d s m
        + (1 - ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s))) atTop
      (𝓝 (ecz_g d s m)) := by
  have hr := ecz_bulkFraction_tendsto (d := d) hd m hm
  rw [ecz_g]
  exact ((hr.mul (tendsto_const_nhds (x := ecz_f d s m))).add
    (((tendsto_const_nhds (x := (1:ℝ))).sub hr).mul
      (tendsto_const_nhds (x := -Real.log (1 - fsc_logistic s)))))


theorem ecz_perEdgeDensityConverges (hd : 1 ≤ d) (s : ℝ)
    (hbox : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card) :
    ecz_PerEdgeDensityConverges d s := by
  classical
  obtain ⟨L, hL⟩ := ecz_dyadic_f_tendsto (d := d) hd s (fun j => hbox _ (agl_K_pos j))
  set c := -Real.log (1 - fsc_logistic s) with hc
  refine ⟨L, ?_⟩
  show Tendsto (fun n => ecz_u d s n / ((boxGraph d n).edgeFinset.card : ℝ)) atTop (𝓝 L)
  have hfdef : (fun n => ecz_u d s n / ((boxGraph d n).edgeFinset.card : ℝ)) = ecz_f d s := by
    funext n; rfl
  rw [hfdef]
  
  have hgK := ecz_g_dyadic_tendsto (d := d) s L hL
  
  have hℓ_tendsto : Tendsto (fun n : ℕ => ((2 * (n : ℝ) + 1) / (2 * n)) * L - c / (2 * n)) atTop
      (𝓝 L) := by
    have h1 : Tendsto (fun n : ℕ => ((2 * (n : ℝ) + 1) / (2 * n)) * L) atTop (𝓝 (1 * L)) :=
      ecz_oddEven_ratio_tendsto.mul tendsto_const_nhds
    have h2 : Tendsto (fun n : ℕ => c / (2 * (n : ℝ))) atTop (𝓝 0) := by
      have hden : Tendsto (fun n : ℕ => (2 * (n : ℝ))) atTop atTop :=
        Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
      exact (tendsto_const_nhds (x := c)).div_atTop hden
    have := h1.sub h2; simpa using this
  
  rw [Metric.tendsto_atTop]
  intro ε hε
  
  obtain ⟨N1, hN1⟩ := (Metric.tendsto_atTop.mp hℓ_tendsto) (ε / 2) (by linarith)
  
  obtain ⟨N0, hN0⟩ := (Metric.tendsto_atTop.mp hgK) (ε / 2) (by linarith)
  set J := N0 with hJ
  have hgJ : ecz_g d s (agl_K J) < L + ε / 2 := by
    have := hN0 J (le_refl _); rw [Real.dist_eq, abs_lt] at this; linarith [this.2]
  
  have hupperseq := ecz_upperSeq_tendsto (d := d) hd s (agl_K J) (agl_K_pos J)
  obtain ⟨N2, hN2⟩ := (Metric.tendsto_atTop.mp hupperseq) (ε / 2) (by linarith)
  refine ⟨max (max N1 N2) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnN2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  rw [Real.dist_eq, abs_lt]
  constructor
  · 
    have hℓle : ((2 * (n : ℝ) + 1) / (2 * n)) * L - c / (2 * n) ≤ ecz_f d s n := by
      have := ecz_f_lower (d := d) hd s n hn1 hbox L hL; rw [← hc] at this; exact this

    have hℓclose : |((2 * (n : ℝ) + 1) / (2 * n)) * L - c / (2 * n) - L| < ε / 2 := by
      have := hN1 n hnN1; rwa [Real.dist_eq] at this
    rw [abs_lt] at hℓclose; linarith [hℓclose.1, hℓle]
  · 
    have hfle : ecz_f d s n
        ≤ (((ecz_T (agl_K J) n) ^ d : ℝ) * ((boxGraph d (agl_K J)).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * ecz_f d s (agl_K J)
          + (1 - ((ecz_T (agl_K J) n) ^ d : ℝ) * ((boxGraph d (agl_K J)).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s)) :=
      ecz_perEdge_vanHove (d := d) (agl_K J) n s (hbox n hn1) (hbox (agl_K J) (agl_K_pos J))
    have hclose : |(((ecz_T (agl_K J) n) ^ d : ℝ) * ((boxGraph d (agl_K J)).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * ecz_f d s (agl_K J)
          + (1 - ((ecz_T (agl_K J) n) ^ d : ℝ) * ((boxGraph d (agl_K J)).edgeFinset.card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ)) * (-Real.log (1 - fsc_logistic s))
          - ecz_g d s (agl_K J)| < ε / 2 := by
      have := hN2 n hnN2; rwa [Real.dist_eq] at this
    rw [abs_lt] at hclose; linarith [hclose.2, hfle, hgJ]

end VanHove


end BoxNesting


section GenuineN1

variable {d : ℕ}


theorem ecz_freeBulkCollapse_n1 (t : ℝ)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (In : (n : ℕ) → Finset (Sym2 (boxVerts d n)))
    (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hin : ∀ n, ∀ e ∈ In n,
      |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e - L| ≤ δ n)
    (hbdy : Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
      atTop (𝓝 0)) :
    Tendsto (fun n => fpd_avgDensity (boxGraph d n) t) atTop (𝓝 L) := by
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  
  rw [← tendsto_add_atTop_iff_nat (f := fun n => fpd_avgDensity (boxGraph d n) t) 1]
  have hrepr : (fun n => fpd_avgDensity (boxGraph d (n + 1)) t)
      = fun n => (1 / ((boxGraph d (n + 1)).edgeFinset.card : ℝ))
          * ∑ e ∈ (boxGraph d (n + 1)).edgeFinset,
              edgeMargProb (fkProb (boxGraph d (n + 1)) (fsc_logistic t) 2) e := by
    funext n; exact adc_avgDensity_eq_sum_edgeMarg (boxGraph d (n + 1)) t
  rw [hrepr]
  exact adc_absavg_tendsto
    (ι := fun n => Sym2 (boxVerts d (n + 1)))
    (En := fun n => (boxGraph d (n + 1)).edgeFinset) (fun n => In (n + 1))
    (fn := fun n e => edgeMargProb (fkProb (boxGraph d (n + 1)) (fsc_logistic t) 2) e)
    L (fun n => δ (n + 1)) (fun n => hIE (n + 1))
    (fun n e _ => adc_edgeMargProb_fkProb_nonneg (boxGraph d (n + 1)) hp hp1 (by norm_num) e)
    (fun n e _ => adc_edgeMargProb_fkProb_le_one (boxGraph d (n + 1)) hp hp1 (by norm_num) e)
    hL0 hL1 (fun n => hδ0 (n + 1)) (hδlim.comp (tendsto_add_atTop_nat 1))
    (fun n => hin (n + 1)) (fun n => hbox1 (n + 1) (by omega))
    (hbdy.comp (tendsto_add_atTop_nat 1))


theorem ecz_wiredBulkCollapse_n1 (t : ℝ)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (In : (n : ℕ) → Finset (Sym2 (boxVerts d n)))
    (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hin : ∀ n, ∀ e ∈ In n,
      |edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e - L| ≤ δ n)
    (hbdy : Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
      atTop (𝓝 0)) :
    Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2 t) atTop (𝓝 L) := by
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  rw [← tendsto_add_atTop_iff_nat
    (f := fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2 t) 1]
  have hrepr : (fun n => wpd_avgWiredDensity (boxGraph d (n + 1)) (boxBoundary d (n + 1)) 2 t)
      = fun n => (1 / ((boxGraph d (n + 1)).edgeFinset.card : ℝ))
          * ∑ e ∈ (boxGraph d (n + 1)).edgeFinset,
              edgeMargProb (wiredFkProb (boxGraph d (n + 1)) (boxBoundary d (n + 1))
                (fsc_logistic t) 2) e := by
    funext n; exact ubd_avgWiredDensity_eq_sum (n + 1) t
  rw [hrepr]
  exact adc_absavg_tendsto
    (ι := fun n => Sym2 (boxVerts d (n + 1)))
    (En := fun n => (boxGraph d (n + 1)).edgeFinset) (fun n => In (n + 1))
    (fn := fun n e => edgeMargProb (wiredFkProb (boxGraph d (n + 1)) (boxBoundary d (n + 1))
      (fsc_logistic t) 2) e)
    L (fun n => δ (n + 1)) (fun n => hIE (n + 1))
    (fun n e _ => ubd_edgeMargProb_wiredFkProb_nonneg (boxGraph d (n + 1)) (boxBoundary d (n + 1))
      hp hp1 (by norm_num) e)
    (fun n e _ => ubd_edgeMargProb_wiredFkProb_le_one (boxGraph d (n + 1)) (boxBoundary d (n + 1))
      hp hp1 (by norm_num) e)
    hL0 hL1 (fun n => hδ0 (n + 1)) (hδlim.comp (tendsto_add_atTop_nat 1))
    (fun n => hin (n + 1)) (fun n => hbox1 (n + 1) (by omega))
    (hbdy.comp (tendsto_add_atTop_nat 1))


theorem ecz_genuineFreeCollapse_n1 (hd : 1 ≤ d) (N : ℕ)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card) :
    fpe2_GenuineFreeCollapse (d := d) N := by
  intro e' he' t
  obtain ⟨In, δ, hIE, hδ0, hδlim, hin, hbdy⟩ :=
    gec_freeBulk_of_sandwich N e' t
      (gec_freeSandwich_of_rotation hd N e' t
        (rot_freeRotationResidue (lt_of_lt_of_le one_pos hd) N e' he' t))
  obtain ⟨hL0, hL1⟩ := ubd_freeEdgeDensity_mem_Icc N e' t
  exact ecz_freeBulkCollapse_n1 t hbox1 _ hL0 hL1 In hIE δ hδ0 hδlim hin hbdy


theorem ecz_genuineWiredCollapse_n1 (hd : 1 ≤ d) (N : ℕ)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card) :
    fpe2_GenuineWiredCollapse (d := d) N := by
  intro e' he' t
  obtain ⟨In, δ, hIE, hδ0, hδlim, hin, hbdy⟩ :=
    gec_wiredBulk_of_sandwich N e' t
      (gec_wiredSandwich_of_rotation hd N e' t
        (rot_wiredRotationResidue (lt_of_lt_of_le one_pos hd) N e' he' t))
  obtain ⟨hL0, hL1⟩ := ubd_wiredEdgeDensity_mem_Icc N e' t
  exact ecz_wiredBulkCollapse_n1 t hbox1 _ hL0 hL1 In hIE δ hδ0 hδlim hin hbdy


theorem ecz_wiredCentered_tendsto_n1 (hd : 1 ≤ d)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (t : ℝ)
    (hfree : Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t))) :
    Tendsto (fun n => cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t) atTop (𝓝 (G t)) := by
  have hsv := fup_surfaceVolume_tendsto_zero d hd
  
  have hdiff : ∀ s : ℝ, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 s
        - wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 s) atTop (𝓝 0) := by
    intro s
    have hbound : ∀ᶠ n in atTop, |ivp2_tiltFreeEnergy (boxGraph d n) 2 s
          - wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 s|
        ≤ ((Finset.univ.filter (boxBoundary d n)).card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ) * Real.log 2 := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact wpd_tiltFreeEnergy_sub_le (boxGraph d n) (boxBoundary d n) (by norm_num)
        (hbox1 n hn) s
    have hsvlog : Tendsto (fun n =>
        ((Finset.univ.filter (boxBoundary d n)).card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)
          * Real.log 2) atTop (𝓝 0) := by
      have := hsv.mul_const (Real.log 2); simpa using this
    refine (tendsto_zero_iff_abs_tendsto_zero _).mpr ?_
    refine squeeze_zero' (Filter.Eventually.of_forall (fun n => abs_nonneg _)) hbound hsvlog
  have hcdiff : Tendsto (fun n => cfe_centered (boxGraph d n) 2 t
        - cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t) atTop (𝓝 0) := by
    have heq : (fun n => cfe_centered (boxGraph d n) 2 t
          - cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t)
        = (fun n => (ivp2_tiltFreeEnergy (boxGraph d n) 2 t
            - wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 t)
          - (ivp2_tiltFreeEnergy (boxGraph d n) 2 0
            - wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 0)) := by
      funext n; unfold cfe_centered cfe_wiredCentered; ring
    rw [heq]
    have := (hdiff t).sub (hdiff 0); simpa using this
  have hwired : Tendsto (fun n => cfe_centered (boxGraph d n) 2 t
        - (cfe_centered (boxGraph d n) 2 t
          - cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t)) atTop (𝓝 (G t - 0)) :=
    hfree.sub hcdiff
  simpa using hwired


theorem ecz_genuineFreeIsLeftDeriv_n1 (N : ℕ)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
    (hcol : fpe2_GenuineFreeCollapse d N) :
    fpe2_GenuineFreeIsLeftDeriv d N G := by
  
  have hshift : ∀ x, Tendsto (fun n => cfe_centered (boxGraph d (n + 1)) 2 x) atTop (𝓝 (G x)) :=
    fun x => (hboxfree x).comp (tendsto_add_atTop_nat 1)
  intro e' he' t
  have hbL : ∀ s, pressureLeftDeriv G s
      ≤ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s) := by
    intro s
    exact fdd_leftDeriv_le_avgLimit
      (fun n => cfe_centered (boxGraph d (n + 1)) 2) G
      (fun n => fpd_avgDensity (boxGraph d (n + 1)))
      (fun n => cfe_centered_convexOn (boxGraph d (n + 1)) 2 (by norm_num) (hbox1 (n + 1) (by omega)))
      (fun n u => cfe_centered_hasDerivAt (boxGraph d (n + 1)) (hbox1 (n + 1) (by omega)) u)
      hshift s _ hG ((hcol e' he' s).comp (tendsto_add_atTop_nat 1))
  have hbR : ∀ s, freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)
      ≤ pressureRightDeriv G s := by
    intro s
    exact fdd_avgLimit_le_rightDeriv
      (fun n => cfe_centered (boxGraph d (n + 1)) 2) G
      (fun n => fpd_avgDensity (boxGraph d (n + 1)))
      (fun n => cfe_centered_convexOn (boxGraph d (n + 1)) 2 (by norm_num) (hbox1 (n + 1) (by omega)))
      (fun n u => cfe_centered_hasDerivAt (boxGraph d (n + 1)) (hbox1 (n + 1) (by omega)) u)
      hshift s _ hG ((hcol e' he' s).comp (tendsto_add_atTop_nat 1))
  exact fdd_eq_leftDeriv_of_bracket_leftContinuous hG hbL hbR
    (osc_freeEdgeDensity_left_continuous d N e' t)


theorem ecz_genuineWiredIsRightDeriv_n1 (hd : 1 ≤ d) (N : ℕ)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
    (hcolfree : fpe2_GenuineFreeCollapse d N)
    (hcolwired : fpe2_GenuineWiredCollapse d N) :
    fpe2_GenuineWiredIsRightDeriv d N G := by
  have hwiredlim : ∀ x,
      Tendsto (fun n => cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 x) atTop (𝓝 (G x)) :=
    fun x => ecz_wiredCentered_tendsto_n1 hd hbox1 x (hboxfree x)
  
  have hshiftF : ∀ x, Tendsto (fun n => cfe_centered (boxGraph d (n + 1)) 2 x) atTop (𝓝 (G x)) :=
    fun x => (hboxfree x).comp (tendsto_add_atTop_nat 1)
  have hshiftW : ∀ x, Tendsto (fun n => cfe_wiredCentered (boxGraph d (n + 1)) (boxBoundary d (n + 1))
      2 x) atTop (𝓝 (G x)) :=
    fun x => (hwiredlim x).comp (tendsto_add_atTop_nat 1)
  intro e' he' t
  have hbL : ∀ s, pressureLeftDeriv G s
      ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s) := by
    intro s
    refine (?_ : pressureLeftDeriv G s
        ≤ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)).trans
      (freeEdgeDensity_q2_le_wiredEdgeDensity d N e' (fsc_logistic_pos s) (fsc_logistic_lt_one s))
    exact fdd_leftDeriv_le_avgLimit
      (fun n => cfe_centered (boxGraph d (n + 1)) 2) G
      (fun n => fpd_avgDensity (boxGraph d (n + 1)))
      (fun n => cfe_centered_convexOn (boxGraph d (n + 1)) 2 (by norm_num) (hbox1 (n + 1) (by omega)))
      (fun n u => cfe_centered_hasDerivAt (boxGraph d (n + 1)) (hbox1 (n + 1) (by omega)) u)
      hshiftF s _ hG ((hcolfree e' he' s).comp (tendsto_add_atTop_nat 1))
  have hbR : ∀ s, wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)
      ≤ pressureRightDeriv G s := by
    intro s
    exact fdd_avgLimit_le_rightDeriv
      (fun n => cfe_wiredCentered (boxGraph d (n + 1)) (boxBoundary d (n + 1)) 2) G
      (fun n => wpd_avgWiredDensity (boxGraph d (n + 1)) (boxBoundary d (n + 1)) 2)
      (fun n => cfe_wiredCentered_convexOn (boxGraph d (n + 1)) (boxBoundary d (n + 1)) 2
        (by norm_num) (hbox1 (n + 1) (by omega)))
      (fun n u => cfe_wiredCentered_hasDerivAt (boxGraph d (n + 1)) (boxBoundary d (n + 1))
        (hbox1 (n + 1) (by omega)) u)
      hshiftW s _ hG ((hcolwired e' he' s).comp (tendsto_add_atTop_nat 1))
  exact fdd_eq_rightDeriv_of_bracket_rightContinuous hG hbL hbR
    (osc_wiredEdgeDensity_right_continuous d N e' t)


theorem ecz_fk_uniqueness_of_centeredData_n1 (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t))) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  fpe2_fk_uniqueness_of_genuine (lt_of_lt_of_le one_pos hd) N eb heb hG
    (ecz_genuineFreeIsLeftDeriv_n1 N hbox1 hG hboxfree
      (ecz_genuineFreeCollapse_n1 hd N hbox1))
    (ecz_genuineWiredIsRightDeriv_n1 hd N hbox1 hG hboxfree
      (ecz_genuineFreeCollapse_n1 hd N hbox1)
      (ecz_genuineWiredCollapse_n1 hd N hbox1))

end GenuineN1
end FK
end StatMech
