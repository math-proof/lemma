/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKGeneralQConsumer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.fkc_rqvanhove.Part4
import Theorem.StatisticalMechanics.Code.FK.FKUniqPerEdge.Part3
import Theorem.StatisticalMechanics.Code.FK.FreeWeakLimit.Part8
import Theorem.StatisticalMechanics.Code.FK.MonotoneWeakLimit.Part2
open scoped BigOperators
open MeasureTheory Filter Topology SimpleGraph Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 2000000


namespace StatMech.FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}


theorem fkgq_wiredFiniteMeasure_succ_real_innerRestrictEvent (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (S : Set (ConfigSpace (Sym2 (boxVerts d n))))
    (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
    (wiredFiniteMeasure d (n + 1) hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxRestrict d n ⁻¹' S)
      = ∑ ρ : ConfigSpace (Sym2 (boxVerts d (n + 1))),
          (innerRestrict d n ⁻¹' S).indicator (fun _ => (1 : ℝ)) ρ
            * bcProb (boxGraph d (n + 1)) (boundaryCliqueGraph (boxBoundary d (n + 1))) p q ρ := by
  have hw : (wiredFiniteMeasure d (n + 1) hp hp1 hq : Measure _).real
        (boxRestrict d n ⁻¹' S)
      = ((wiredFkPMF (boxGraph d (n + 1)) (boxBoundary d (n + 1)) hp hp1 hq).toMeasure
          (extendEdge d (n + 1) ⁻¹' (boxRestrict d n ⁻¹' S))).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d (n + 1)) hmeas]
  have hpre : extendEdge d (n + 1) ⁻¹' (boxRestrict d n ⁻¹' S)
      = innerRestrict d n ⁻¹' S := by
    ext ρ
    simp only [Set.mem_preimage, boxRestrict_extendEdge_succ]
  rw [hw, hpre, wiredFkPMF_toMeasure_toReal d (n + 1) hp hp1 hq]
  exact Finset.sum_congr rfl (fun ρ _ => by rw [bcProb_clique_eq_wiredFkProb])


theorem fkgq_wiredFiniteMeasure_real_boxRestrictEvent (m : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (S : Set (ConfigSpace (Sym2 (boxVerts d m))))
    (hmeas : MeasurableSet (boxRestrict d m ⁻¹' S)) :
    (wiredFiniteMeasure d m hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxRestrict d m ⁻¹' S)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d m)),
          S.indicator (fun _ => (1 : ℝ)) ω
            * wiredFkProb (boxGraph d m) (boxBoundary d m) p q ω := by
  have hw : (wiredFiniteMeasure d m hp hp1 hq : Measure _).real (boxRestrict d m ⁻¹' S)
      = ((wiredFkPMF (boxGraph d m) (boxBoundary d m) hp hp1 hq).toMeasure
          (extendEdge d m ⁻¹' (boxRestrict d m ⁻¹' S))).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d m) hmeas]
  have hpre : extendEdge d m ⁻¹' (boxRestrict d m ⁻¹' S) = S := by
    ext ω
    simp only [Set.mem_preimage, boxRestrict_extendEdge]
  rw [hw, hpre, wiredFkPMF_toMeasure_toReal d m hp hp1 hq]


theorem fkgq_wiredFiniteMeasure_succ_le_smallerBox (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hS : IsIncreasing S)
    (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
    (wiredFiniteMeasure d (n + 1) hp hp1 (zero_lt_one.trans_le hq)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S)
      ≤ ∑ ω, S.indicator (fun _ => (1 : ℝ)) ω
          * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  rw [fkgq_wiredFiniteMeasure_succ_real_innerRestrictEvent n hp hp1
    (zero_lt_one.trans_le hq) S hmeas]
  exact wiredSucc_bcProb_innerEvent_le n hp hp1 hq hS


theorem fkgq_freeFiniteMeasure_smallerBox_le_succ (n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hS : IsIncreasing S)
    (hmeas : MeasurableSet (boxRestrict d n ⁻¹' S)) :
    (∑ ω, S.indicator (fun _ => (1 : ℝ)) ω * fkProb (boxGraph d n) p q ω)
      ≤ (freeFiniteMeasure d (n + 1) hp hp1 (zero_lt_one.trans_le hq)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d n ⁻¹' S) := by
  rw [freeFiniteMeasure_succ_real_innerRestrictEvent n hp hp1
    (zero_lt_one.trans_le hq) S hmeas]
  exact freeSucc_fkProb_innerEvent_le n hp hp1 hq hS


theorem fkgq_free_succ (N m : ℕ) (hNm : N ≤ m) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S)
      ≤ (freeFiniteMeasure d (m + 1) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  set T := boxRestrictLE d hNm ⁻¹' S with hT
  have hTinc : IsIncreasing T := fun a b hab ha => hS (boxRestrictLE_monotone d hNm hab) ha
  have heq : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext ω; simp only [hT, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [heq, freeFiniteMeasure_real_boxRestrictEvent m hp hp1
    (zero_lt_one.trans_le hq) T hmeas]
  exact fkgq_freeFiniteMeasure_smallerBox_le_succ m hp hp1 hq hTinc hmeas


theorem fkgq_wired_succ (N m : ℕ) (hNm : N ≤ m) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    (wiredFiniteMeasure d (m + 1) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S)
      ≤ (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S) := by
  set T := boxRestrictLE d hNm ⁻¹' S with hT
  have hTinc : IsIncreasing T := fun a b hab ha => hS (boxRestrictLE_monotone d hNm hab) ha
  have heq : boxRestrict d N ⁻¹' S = boxRestrict d m ⁻¹' T := by
    ext ω; simp only [hT, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [heq, fkgq_wiredFiniteMeasure_real_boxRestrictEvent m hp hp1
    (zero_lt_one.trans_le hq) T hmeas]
  exact fkgq_wiredFiniteMeasure_succ_le_smallerBox m hp hp1 hq hTinc hmeas


theorem fkgq_free_infinite_measure (N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    Tendsto (fun m => (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S)) atTop
      (nhds ((freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S))) := by
  set f := fun m => (freeFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
    (boxRestrict d N ⁻¹' S) with hf
  have hmono : Monotone (fun k => f (N + k)) := by
    apply monotone_nat_of_le_succ
    intro k
    simpa [f, Nat.add_assoc] using
      fkgq_free_succ N (N + k) (Nat.le_add_right N k) hp hp1 hq hS
  have hbdd : BddAbove (Set.range fun k => f (N + k)) :=
    ⟨1, by rintro x ⟨k, rfl⟩; exact measureReal_le_one⟩
  set L := ⨆ k, f (N + k) with hL
  have hshift : Tendsto (fun k => f (N + k)) atTop (nhds L) := by
    rw [hL]
    exact tendsto_atTop_ciSup hmono hbdd
  have hfull : Tendsto f atTop (nhds L) := by
    have hk : Tendsto (fun k => f (k + N)) atTop (nhds L) := by
      simpa [Nat.add_comm] using hshift
    exact (Filter.tendsto_add_atTop_iff_nat N).mp hk
  obtain ⟨ψ, hψ, hconv⟩ := freeInfiniteVolume_isLimit d hp hp1 (zero_lt_one.trans_le hq)
  have hport := hconv.tendsto_real_of_isClopen
    (fkFreeLimit_isClopen_preimage N S)
  have hsub := hfull.comp hψ.tendsto_atTop
  have heq : L = (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
      (boxRestrict d N ⁻¹' S) := tendsto_nhds_unique hsub hport
  rwa [heq] at hfull


theorem fkgq_wired_infinite_measure (N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {S : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hS : IsIncreasing S) :
    Tendsto (fun m => (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S)) atTop
      (nhds ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' S))) := by
  set f := fun m => (wiredFiniteMeasure d m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
    (boxRestrict d N ⁻¹' S) with hf
  have hanti : Antitone (fun k => f (N + k)) := by
    apply antitone_nat_of_succ_le
    intro k
    simpa [f, Nat.add_assoc] using
      fkgq_wired_succ N (N + k) (Nat.le_add_right N k) hp hp1 hq hS
  have hbdd : BddBelow (Set.range fun k => f (N + k)) :=
    ⟨0, by rintro x ⟨k, rfl⟩; exact measureReal_nonneg⟩
  set L := ⨅ k, f (N + k) with hL
  have hshift : Tendsto (fun k => f (N + k)) atTop (nhds L) := by
    rw [hL]
    exact tendsto_atTop_ciInf hanti hbdd
  have hfull : Tendsto f atTop (nhds L) := by
    have hk : Tendsto (fun k => f (k + N)) atTop (nhds L) := by
      simpa [Nat.add_comm] using hshift
    exact (Filter.tendsto_add_atTop_iff_nat N).mp hk
  obtain ⟨ψ, hψ, hconv⟩ := wiredInfiniteVolume_isLimit d hp hp1 (zero_lt_one.trans_le hq)
  have hport := hconv.tendsto_real_of_isClopen
    (fkWiredLimit_isClopen_preimage N S)
  have hsub := hfull.comp hψ.tendsto_atTop
  have heq : L = (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
      (boxRestrict d N ⁻¹' S) := tendsto_nhds_unique hsub hport
  rwa [heq] at hfull


theorem fkgq_ivp_eq_edgeFE (d n : ℕ) (s q : ℝ) (hq : 0 < q)
    (hE : 0 < (boxGraph d n).edgeFinset.card) :
    ivp2_tiltFreeEnergy (boxGraph d n) q s
      = (ecz_NE (boxGraph d n) : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ) * Real.log 2
        + StatMech.Walls.fkc_edgeFreeEnergy d s q n := by
  unfold ivp2_tiltFreeEnergy StatMech.Walls.fkc_edgeFreeEnergy
  set p := fsc_logistic s
  have hp0 : (0 : ℝ) < p := fsc_logistic_pos s
  have hp1 : p < 1 := fsc_logistic_lt_one s
  have hfact := ecz_factorization (boxGraph d n) p q
  have hZE : 0 < ecz_fkZEdge (boxGraph d n) p q := ecz_fkZEdge_pos _ hp0 hp1 hq
  have h2 : (0 : ℝ) < (2 : ℝ) ^ ecz_NE (boxGraph d n) := by positivity
  rw [hfact, Real.log_mul h2.ne' hZE.ne', Real.log_pow]
  have hEne : ((boxGraph d n).edgeFinset.card : ℝ) ≠ 0 := by exact_mod_cast hE.ne'
  field_simp
  ring


theorem fkgq_centered_eq_edgeFE (d n : ℕ) (s q : ℝ) (hq : 0 < q)
    (hE : 0 < (boxGraph d n).edgeFinset.card) :
    cfe_centered (boxGraph d n) q s
      = StatMech.Walls.fkc_edgeFreeEnergy d s q n
        - StatMech.Walls.fkc_edgeFreeEnergy d 0 q n := by
  unfold cfe_centered
  rw [fkgq_ivp_eq_edgeFE d n s q hq hE, fkgq_ivp_eq_edgeFE d n 0 q hq hE]
  ring


theorem fkgq_centeredConvergence (d : ℕ) (hd : 1 ≤ d) (q : ℝ) (hq : 1 ≤ q) :
    ∃ G : ℝ → ℝ,
      (∀ s, Tendsto (fun n => cfe_centered (boxGraph d n) q s) atTop (nhds (G s)))
        ∧ ConvexOn ℝ Set.univ G ∧ G 0 = 0 := by
  have hedge : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card :=
    fun n hn => ecz_box_edge_pos d hd hn
  have hconvEdge : ∀ s, ∃ L : ℝ,
      Tendsto (fun n => StatMech.Walls.fkc_edgeFreeEnergy d s q n) atTop (nhds L) := by
    intro s
    obtain ⟨ρ, hρ⟩ := StatMech.Walls.fkc_perEdgeDensityConverges d hd s q hq
    refine ⟨Real.log (1 + Real.exp s) - ρ, ?_⟩
    have h := hρ.const_sub (Real.log (1 + Real.exp s))
    have heq : (fun n => StatMech.Walls.fkc_edgeFreeEnergy d s q n)
        = fun n => Real.log (1 + Real.exp s) - StatMech.Walls.fkc_f d s q n := by
      funext n
      rw [StatMech.Walls.fkc_edgeFreeEnergy_eq]
      ring
    rw [heq]
    simpa using h
  have hcent : ∀ s, ∃ L : ℝ,
      Tendsto (fun n => cfe_centered (boxGraph d n) q s) atTop (nhds L) := by
    intro s
    obtain ⟨Ls, hLs⟩ := hconvEdge s
    obtain ⟨L0, hL0⟩ := hconvEdge 0
    refine ⟨Ls - L0, ?_⟩
    refine Tendsto.congr' ?_ (hLs.sub hL0)
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (fkgq_centered_eq_edgeFE d n s q (zero_lt_one.trans_le hq) (hedge n hn)).symm
  classical
  let G : ℝ → ℝ := fun s => (hcent s).choose
  have hGlim : ∀ s, Tendsto (fun n => cfe_centered (boxGraph d n) q s) atTop (nhds (G s)) :=
    fun s => (hcent s).choose_spec
  refine ⟨G, hGlim, ?_, ?_⟩
  · refine ivp2_convexOn_of_tendsto (l := (atTop : Filter ℕ))
      (fun n => cfe_centered (boxGraph d (n + 1)) q) G
      (fun n => cfe_centered_convexOn (boxGraph d (n + 1)) q
        (zero_lt_one.trans_le hq) (hedge (n + 1) (by omega))) ?_
    intro s
    exact (hGlim s).comp (tendsto_add_atTop_nat 1)
  · have hzero : Tendsto (fun n => cfe_centered (boxGraph d n) q 0) atTop (nhds 0) := by
      simp only [cfe_centered_zero]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique (hGlim 0) hzero


end StatMech.FK
