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
import Def.StatisticalMechanics.Code.FK.FKGeneralQConsumer.Part2
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


theorem fkgq_freeMass_nonneg (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ) :
    0 ≤ fkgq_freeMass d N q hq s := fun _ => measureReal_nonneg

theorem fkgq_wiredMass_nonneg (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ) :
    0 ≤ fkgq_wiredMass d N q hq s := fun _ => measureReal_nonneg

theorem fkgq_freeMass_sum_one (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ) :
    ∑ ω, fkgq_freeMass d N q hq s ω = 1 :=
  fuc_sum_real_preimage_eq_one _ (boxRestrict d N) (continuous_boxRestrict d N).measurable

theorem fkgq_wiredMass_sum_one (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ) :
    ∑ ω, fkgq_wiredMass d N q hq s ω = 1 :=
  fuc_sum_real_preimage_eq_one _ (boxRestrict d N) (continuous_boxRestrict d N).measurable

theorem fkgq_eventMass_free (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ)
    (A : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    eventMassProb (fkgq_freeMass d N q hq s) A
      = (freeInfiniteVolume d (fsc_logistic_pos s) (fsc_logistic_lt_one s)
          (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' A) := by
  unfold eventMassProb fkgq_freeMass
  rw [fuc_real_preimage_eq_indicator_sum _ (boxRestrict d N)
    (continuous_boxRestrict d N).measurable A]

theorem fkgq_eventMass_wired (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ)
    (A : Set (ConfigSpace (Sym2 (boxVerts d N)))) :
    eventMassProb (fkgq_wiredMass d N q hq s) A
      = (wiredInfiniteVolume d (fsc_logistic_pos s) (fsc_logistic_lt_one s)
          (zero_lt_one.trans_le hq) : Measure _).real (boxRestrict d N ⁻¹' A) := by
  unfold eventMassProb fkgq_wiredMass
  rw [fuc_real_preimage_eq_indicator_sum _ (boxRestrict d N)
    (continuous_boxRestrict d N).measurable A]


theorem fkgq_edgeMarg_free (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ)
    (e : Sym2 (boxVerts d N)) :
    edgeMargProb (fkgq_freeMass d N q hq s) e
      = freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic s) := by
  rw [fuc_edgeMargProb_eq_eventMassProb, fkgq_eventMass_free]
  unfold freeEdgeDensity
  rw [dif_pos ⟨fsc_logistic_pos s, fsc_logistic_lt_one s, zero_lt_one.trans_le hq⟩,
    fkEdgeOpenEvent_edgeIncl_eq_boxRestrict]


theorem fkgq_edgeMarg_wired (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ)
    (e : Sym2 (boxVerts d N)) :
    edgeMargProb (fkgq_wiredMass d N q hq s) e
      = wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic s) := by
  rw [fuc_edgeMargProb_eq_eventMassProb, fkgq_eventMass_wired]
  unfold wiredEdgeDensity
  rw [dif_pos ⟨fsc_logistic_pos s, fsc_logistic_lt_one s, zero_lt_one.trans_le hq⟩,
    fkEdgeOpenEvent_edgeIncl_eq_boxRestrict]


theorem fkgq_freeIV_le_wiredIV (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 (boxVerts d N)))} (hA : IsIncreasing A) :
    (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' A)
      ≤ (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d N ⁻¹' A) := by
  have hf := fkgq_free_infinite_measure N hp hp1 hq hA
  have hw := fkgq_wired_infinite_measure N hp hp1 hq hA
  refine le_of_tendsto_of_tendsto hf hw (Filter.Eventually.of_forall (fun m => ?_))
  exact freeFiniteMeasure_dominated d m hp hp1 hq _
    ((continuous_boxRestrict d N).measurable MeasurableSet.of_discrete)
    (fun a b hab ha => hA (monotone_boxRestrict d N hab) ha)


theorem fkgq_dominated (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) (s : ℝ) :
    measOfMass (fkgq_freeMass d N q hq s) ≼ measOfMass (fkgq_wiredMass d N q hq s) := by
  intro A _ hA
  rw [measOfMass_real_eq_indicator_sum _ (fkgq_freeMass_nonneg d N q hq s) A,
    measOfMass_real_eq_indicator_sum _ (fkgq_wiredMass_nonneg d N q hq s) A]
  change eventMassProb (fkgq_freeMass d N q hq s) A
    ≤ eventMassProb (fkgq_wiredMass d N q hq s) A
  rw [fkgq_eventMass_free, fkgq_eventMass_wired]
  exact fkgq_freeIV_le_wiredIV d N (fsc_logistic_pos s) (fsc_logistic_lt_one s) hq hA


theorem fkgq_hcoup (d N : ℕ) (q : ℝ) (hq : 1 ≤ q) :
    ∀ s : ℝ, ∃ P : ConfigSpace (Sym2 (boxVerts d N)) × ConfigSpace (Sym2 (boxVerts d N)) → ℝ,
      IsMonotoneCouplingFun P (fkgq_freeMass d N q hq s) (fkgq_wiredMass d N q hq s) :=
  fun s => fuc_isMonotoneCouplingFun_of_dominated
    (fkgq_freeMass_nonneg d N q hq s) (fkgq_wiredMass_nonneg d N q hq s)
    (fkgq_freeMass_sum_one d N q hq s) (fkgq_wiredMass_sum_one d N q hq s)
    (fkgq_dominated d N q hq s)


theorem fkgq_free_finite_mass_eq_edgeMarg (N m : ℕ) (hNm : N ≤ m)
    (e : Sym2 (boxVerts d N)) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    (freeFiniteMeasure d m hp hp1 hq : Measure _).real
        (boxRestrict d N ⁻¹' boxEdgeOpenEvent d N e)
      = edgeMargProb (fkProb (boxGraph d m) p q) (innerEdgeLE d hNm e) := by
  set T := boxRestrictLE d hNm ⁻¹' boxEdgeOpenEvent d N e with hT
  have hTeq : T = boxEdgeOpenEvent d m (innerEdgeLE d hNm e) := by
    ext η
    simp only [hT, boxEdgeOpenEvent, Set.mem_preimage, Set.mem_setOf_eq, boxRestrictLE]
  have heq : boxRestrict d N ⁻¹' boxEdgeOpenEvent d N e = boxRestrict d m ⁻¹' T := by
    ext ω; simp only [hT, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [heq, freeFiniteMeasure_real_boxRestrictEvent m hp hp1 hq T hmeas, hTeq]
  unfold edgeMargProb
  exact Finset.sum_congr rfl (fun ω _ => by rw [dfi_indicator_boxEdgeOpenEvent])


theorem fkgq_wired_finite_mass_eq_edgeMarg (N m : ℕ) (hNm : N ≤ m)
    (e : Sym2 (boxVerts d N)) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    (wiredFiniteMeasure d m hp hp1 hq : Measure _).real
        (boxRestrict d N ⁻¹' boxEdgeOpenEvent d N e)
      = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p q)
          (innerEdgeLE d hNm e) := by
  set T := boxRestrictLE d hNm ⁻¹' boxEdgeOpenEvent d N e with hT
  have hTeq : T = boxEdgeOpenEvent d m (innerEdgeLE d hNm e) := by
    ext η
    simp only [hT, boxEdgeOpenEvent, Set.mem_preimage, Set.mem_setOf_eq, boxRestrictLE]
  have heq : boxRestrict d N ⁻¹' boxEdgeOpenEvent d N e = boxRestrict d m ⁻¹' T := by
    ext ω; simp only [hT, Set.mem_preimage, boxRestrictLE_boxRestrict]
  have hmeas : MeasurableSet (boxRestrict d m ⁻¹' T) :=
    (continuous_boxRestrict d m).measurable MeasurableSet.of_discrete
  rw [heq, fkgq_wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 hq T hmeas, hTeq]
  unfold edgeMargProb
  exact Finset.sum_congr rfl (fun ω _ => by rw [dfi_indicator_boxEdgeOpenEvent])


theorem fkgq_free_density_eq_limit (N : ℕ) (e : Sym2 (boxVerts d N))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun k => edgeMargProb (fkProb (boxGraph d (N + k)) p q)
        (innerEdgeLE d (Nat.le_add_right N k) e)) atTop
      (nhds (freeEdgeDensity d q (edgeIncl d N e) p)) := by
  have hm := fkgq_free_infinite_measure N hp hp1 hq (boxEdgeOpenEvent_isIncreasing d N e)
  have hm' := hm.comp (dfi_tendsto_add_left N)
  have hdens : (freeInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
      (boxRestrict d N ⁻¹' boxEdgeOpenEvent d N e)
      = freeEdgeDensity d q (edgeIncl d N e) p := by
    unfold freeEdgeDensity
    rw [dif_pos ⟨hp, hp1, zero_lt_one.trans_le hq⟩, fkEdgeOpenEvent_edgeIncl_eq_boxRestrict]
  rw [hdens] at hm'
  refine hm'.congr (fun k => ?_)
  change (freeFiniteMeasure d (N + k) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
      (boxRestrict d N ⁻¹' boxEdgeOpenEvent d N e) = _
  exact fkgq_free_finite_mass_eq_edgeMarg N (N + k) (Nat.le_add_right N k) e hp hp1
    (zero_lt_one.trans_le hq)


theorem fkgq_wired_density_eq_limit (N : ℕ) (e : Sym2 (boxVerts d N))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto (fun k => edgeMargProb
        (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p q)
        (innerEdgeLE d (Nat.le_add_right N k) e)) atTop
      (nhds (wiredEdgeDensity d q (edgeIncl d N e) p)) := by
  have hm := fkgq_wired_infinite_measure N hp hp1 hq (boxEdgeOpenEvent_isIncreasing d N e)
  have hm' := hm.comp (dfi_tendsto_add_left N)
  have hdens : (wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
      (boxRestrict d N ⁻¹' boxEdgeOpenEvent d N e)
      = wiredEdgeDensity d q (edgeIncl d N e) p := by
    unfold wiredEdgeDensity
    rw [dif_pos ⟨hp, hp1, zero_lt_one.trans_le hq⟩, fkEdgeOpenEvent_edgeIncl_eq_boxRestrict]
  rw [hdens] at hm'
  refine hm'.congr (fun k => ?_)
  change (wiredFiniteMeasure d (N + k) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
      (boxRestrict d N ⁻¹' boxEdgeOpenEvent d N e) = _
  exact fkgq_wired_finite_mass_eq_edgeMarg N (N + k) (Nat.le_add_right N k) e hp hp1
    (zero_lt_one.trans_le hq)


theorem fkgq_box_free_edgeMarg_inv (S : BoxSym d) (m : ℕ) (p q : ℝ)
    (e : Sym2 (boxVerts d m)) :
    edgeMargProb (fkProb (boxGraph d m) p q) (Sym2.map (S.lift m) e)
      = edgeMargProb (fkProb (boxGraph d m) p q) e :=
  fkTI_edgeMargProb_fkProb_reCfg (boxGraph d m) (S.lift m) (S.lift_adj m) p q e


theorem fkgq_box_wired_edgeMarg_inv (S : BoxSym d) (m : ℕ) (p q : ℝ)
    (e : Sym2 (boxVerts d m)) :
    edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p q)
        (Sym2.map (S.lift m) e)
      = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p q) e :=
  fkTI_edgeMargProb_wiredFkProb_reCfg (boxGraph d m) (boxBoundary d m) (S.lift m)
    (S.lift_adj m) (S.lift_boundary m) p q e


theorem fkgq_free_density_boxSym (S : BoxSym d) (N : ℕ) (e : Sym2 (boxVerts d N))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (edgeIncl d N e) p
      = freeEdgeDensity d q (edgeIncl d N (Sym2.map (S.lift N) e)) p := by
  have h1 := fkgq_free_density_eq_limit N e hp hp1 hq
  have h2 := fkgq_free_density_eq_limit N (Sym2.map (S.lift N) e) hp hp1 hq
  refine tendsto_nhds_unique h1 (h2.congr (fun k => ?_))
  rw [← S.lift_innerEdgeLE (Nat.le_add_right N k) e,
    fkgq_box_free_edgeMarg_inv S (N + k) p q]


theorem fkgq_wired_density_boxSym (S : BoxSym d) (N : ℕ) (e : Sym2 (boxVerts d N))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredEdgeDensity d q (edgeIncl d N e) p
      = wiredEdgeDensity d q (edgeIncl d N (Sym2.map (S.lift N) e)) p := by
  have h1 := fkgq_wired_density_eq_limit N e hp hp1 hq
  have h2 := fkgq_wired_density_eq_limit N (Sym2.map (S.lift N) e) hp hp1 hq
  refine tendsto_nhds_unique h1 (h2.congr (fun k => ?_))
  rw [← S.lift_innerEdgeLE (Nat.le_add_right N k) e,
    fkgq_box_wired_edgeMarg_inv S (N + k) p q]


theorem fkgq_free_per_edge_upper (n : ℕ) (e : Sym2 (boxVerts d n))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    edgeMargProb (fkProb (boxGraph d n) p q) e
      ≤ freeEdgeDensity d q (edgeIncl d n e) p := by
  have hlim := fkgq_free_density_eq_limit n e hp hp1 hq
  have hmono : Monotone (fun k =>
      (freeFiniteMeasure d (n + k) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d n ⁻¹' boxEdgeOpenEvent d n e)) := by
    apply monotone_nat_of_le_succ
    intro k
    simpa [Nat.add_assoc] using
      fkgq_free_succ n (n + k) (Nat.le_add_right n k) hp hp1 hq
        (boxEdgeOpenEvent_isIncreasing d n e)
  have hseq : ∀ k, edgeMargProb (fkProb (boxGraph d n) p q) e ≤
      edgeMargProb (fkProb (boxGraph d (n + k)) p q)
        (innerEdgeLE d (Nat.le_add_right n k) e) := by
    intro k
    have hk := hmono (Nat.zero_le k)
    dsimp only at hk
    rw [Nat.add_zero,
      fkgq_free_finite_mass_eq_edgeMarg n n (le_refl n) e hp hp1 (zero_lt_one.trans_le hq),
      fkgq_free_finite_mass_eq_edgeMarg n (n + k) (Nat.le_add_right n k) e hp hp1
        (zero_lt_one.trans_le hq)] at hk
    rwa [bdp_innerEdgeLE_refl n e] at hk
  exact ge_of_tendsto hlim (Filter.Eventually.of_forall hseq)


theorem fkgq_wired_per_edge_lower (n : ℕ) (e : Sym2 (boxVerts d n))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredEdgeDensity d q (edgeIncl d n e) p
      ≤ edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p q) e := by
  have hlim := fkgq_wired_density_eq_limit n e hp hp1 hq
  have hanti : Antitone (fun k =>
      (wiredFiniteMeasure d (n + k) hp hp1 (zero_lt_one.trans_le hq) : Measure _).real
        (boxRestrict d n ⁻¹' boxEdgeOpenEvent d n e)) := by
    apply antitone_nat_of_succ_le
    intro k
    simpa [Nat.add_assoc] using
      fkgq_wired_succ n (n + k) (Nat.le_add_right n k) hp hp1 hq
        (boxEdgeOpenEvent_isIncreasing d n e)
  have hseq : ∀ k, edgeMargProb
      (wiredFkProb (boxGraph d (n + k)) (boxBoundary d (n + k)) p q)
        (innerEdgeLE d (Nat.le_add_right n k) e)
      ≤ edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p q) e := by
    intro k
    have hk := hanti (Nat.zero_le k)
    dsimp only at hk
    rw [Nat.add_zero,
      fkgq_wired_finite_mass_eq_edgeMarg n n (le_refl n) e hp hp1 (zero_lt_one.trans_le hq),
      fkgq_wired_finite_mass_eq_edgeMarg n (n + k) (Nat.le_add_right n k) e hp hp1
        (zero_lt_one.trans_le hq)] at hk
    rwa [bdp_innerEdgeLE_refl n e] at hk
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hseq)


theorem fkgq_free_offCentre_lower (R n : ℕ) (hRn : R ≤ n) (hmn : n - R ≤ n)
    (u v : boxVerts d (n - R)) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (c0 : (0 : Site d) ∈ box d R) (cw : ((v : Site d) - (u : Site d)) ∈ box d R) :
    edgeMargProb (fkProb (boxGraph d R) p q)
        (s((⟨(0 : Site d), c0⟩ : boxVerts d R),
          (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d R)))
      ≤ edgeMargProb (fkProb (boxGraph d n) p q)
          (innerEdgeLE d hmn (s(u, v) : Sym2 (boxVerts d (n - R)))) := by
  set a : Site d := (u : Site d) with ha
  have ha_box : a ∈ box d (n - R) := u.2
  have hsub : fvs_transBox d R a ⊆ box d n := by
    intro y hy i
    have hyi : ((y - a) i).natAbs ≤ R := hy i
    have hai : (a i).natAbs ≤ n - R := ha_box i
    have hsubc : (y - a) i = y i - a i := by simp [Pi.sub_apply]
    have hyeq : y i = (y i - a i) + a i := by ring
    calc (y i).natAbs = ((y i - a i) + a i).natAbs := by rw [← hyeq]
      _ ≤ (y i - a i).natAbs + (a i).natAbs := Int.natAbs_add_le _ _
      _ = ((y - a) i).natAbs + (a i).natAbs := by rw [hsubc]
      _ ≤ R + (n - R) := Nat.add_le_add hyi hai
      _ = n := by omega
  set ce : Sym2 (boxVerts d R) :=
    s((⟨(0 : Site d), c0⟩ : boxVerts d R),
      (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d R)) with hce
  have htrans := (fvs_box_translation_edgeMarg d R a ce (p := p) (q := q)).2
  set eS : Sym2 (fvs_transBoxVerts d R a) := Sym2.map (fvs_transEquiv d R a) ce with heS
  have hdom := bdp_latticeFree_multiMass_dominated (Sin := fvs_transBox d R a) (Sout := box d n)
    (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub) hp hp1 hq
    ({eS} : Finset (Sym2 (fvs_transBoxVerts d R a)))
  rw [Finset.image_singleton, ← bdp_edgeMargProb_eq_med_singleton,
    ← bdp_edgeMargProb_eq_med_singleton] at hdom
  rw [show edgeMargProb (fkProb (boxGraph d R) p q) ce
        = edgeMargProb (fkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) p q) eS
      from htrans.symm]
  refine hdom.trans (le_of_eq ?_)
  congr 1
  exact ocs_innerEdge_recentre d R n (n - R) hmn u v hsub c0 cw


theorem fkgq_wired_offCentre_upper (R n : ℕ) (hR : 1 ≤ R) (hRn1 : R + 1 ≤ n)
    (hmn : n - R - 1 ≤ n) (u v : boxVerts d (n - R - 1))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (c0 : (0 : Site d) ∈ box d R) (cw : ((v : Site d) - (u : Site d)) ∈ box d R) :
    edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p q)
        (innerEdgeLE d hmn (s(u, v) : Sym2 (boxVerts d (n - R - 1))))
      ≤ edgeMargProb (wiredFkProb (boxGraph d R) (boxBoundary d R) p q)
          (s((⟨(0 : Site d), c0⟩ : boxVerts d R),
            (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d R))) := by
  set a : Site d := (u : Site d) with ha
  have ha_box : a ∈ box d (n - R - 1) := u.2
  have hsub : fvs_transBox d R a ⊆ box d n := by
    intro y hy i
    have hyi : ((y - a) i).natAbs ≤ R := hy i
    have hai : (a i).natAbs ≤ n - R - 1 := ha_box i
    have hsubc : (y - a) i = y i - a i := by simp [Pi.sub_apply]
    have hyeq : y i = (y i - a i) + a i := by ring
    calc (y i).natAbs = ((y i - a i) + a i).natAbs := by rw [← hyeq]
      _ ≤ (y i - a i).natAbs + (a i).natAbs := Int.natAbs_add_le _ _
      _ = ((y - a) i).natAbs + (a i).natAbs := by rw [hsubc]
      _ ≤ R + (n - R - 1) := Nat.add_le_add hyi hai
      _ ≤ n := by omega
  set ce : Sym2 (boxVerts d R) :=
    s((⟨(0 : Site d), c0⟩ : boxVerts d R),
      (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d R)) with hce
  have htrans := (fvs_box_translation_edgeMarg d R a ce (p := p) (q := q)).1
  set eS : Sym2 (fvs_transBoxVerts d R a) := Sym2.map (fvs_transEquiv d R a) ce with heS
  have hdom := ocd_latticeWired_multiMass_dominated (Sin := fvs_transBox d R a) (Sout := box d n)
    (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
    (boxBoundary d n) (fvs_transBoxBoundary d R a)
    (ocs_wired_margin d R n a ha_box hRn1 hsub) (flc_hbdryIn_transBox hR a)
    hp hp1 hq ({eS} : Finset (Sym2 (fvs_transBoxVerts d R a)))
  rw [Finset.image_singleton, ← bdp_edgeMargProb_eq_med_singleton,
    ← bdp_edgeMargProb_eq_med_singleton] at hdom
  rw [show edgeMargProb (wiredFkProb (boxGraph d R) (boxBoundary d R) p q) ce
        = edgeMargProb
          (wiredFkProb (fvs_transBoxGraph d R a) (fvs_transBoxBoundary d R a) p q) eS
      from htrans.symm]
  refine le_trans (le_of_eq ?_) hdom
  congr 1
  exact (ocs_innerEdge_recentre d R n (n - R - 1) hmn u v hsub c0 cw).symm


theorem fkgq_transBox_subset_box_add (m : ℕ) (a : Site d) :
    fvs_transBox d m a ⊆ box d (m + Finset.univ.sup (fun i => (a i).natAbs)) := by
  intro y hy i
  have hyi : ((y - a) i).natAbs ≤ m := hy i
  have hai : (a i).natAbs ≤ Finset.univ.sup (fun j => (a j).natAbs) :=
    Finset.le_sup (f := fun j => (a j).natAbs) (Finset.mem_univ i)
  have hsubc : (y - a) i = y i - a i := by simp [Pi.sub_apply]
  have hyeq : y i = (y i - a i) + a i := by ring
  calc (y i).natAbs = ((y i - a i) + a i).natAbs := by rw [← hyeq]
    _ ≤ (y i - a i).natAbs + (a i).natAbs := Int.natAbs_add_le _ _
    _ = ((y - a) i).natAbs + (a i).natAbs := by rw [hsubc]
    _ ≤ m + Finset.univ.sup (fun j => (a j).natAbs) := Nat.add_le_add hyi hai


theorem fkgq_density_translate_order (N : ℕ) (eb : Sym2 (boxVerts d N)) (a : Site d)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (edgeIncl d N eb) p
        ≤ freeEdgeDensity d q (Sym2.map (fun x => x + a) (edgeIncl d N eb)) p
      ∧ wiredEdgeDensity d q (Sym2.map (fun x => x + a) (edgeIncl d N eb)) p
        ≤ wiredEdgeDensity d q (edgeIncl d N eb) p := by
  induction eb with
  | h u v =>
    set C := Finset.univ.sup (fun i => (a i).natAbs) with hC
    have hua : (u : Site d) + a ∈ box d (N + C + 1) := by
      intro i
      have hu := u.2 i
      have ha : (a i).natAbs ≤ C := by
        rw [hC]; exact Finset.le_sup (f := fun j => (a j).natAbs) (Finset.mem_univ i)
      exact le_trans (le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add hu ha)) (by omega)
    have hva : (v : Site d) + a ∈ box d (N + C + 1) := by
      intro i
      have hv := v.2 i
      have ha : (a i).natAbs ≤ C := by
        rw [hC]; exact Finset.le_sup (f := fun j => (a j).natAbs) (Finset.mem_univ i)
      exact le_trans (le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add hv ha)) (by omega)
    set ebA : Sym2 (boxVerts d (N + C + 1)) :=
      s((⟨(u : Site d) + a, hua⟩ : boxVerts d (N + C + 1)),
        (⟨(v : Site d) + a, hva⟩ : boxVerts d (N + C + 1))) with hebA
    have hInclA : edgeIncl d (N + C + 1) ebA
        = Sym2.map (fun x => x + a) (edgeIncl d N (s(u, v))) := by
      rw [hebA]
      simp only [edgeIncl, Sym2.map_mk]
    have hfreeL := fkgq_free_density_eq_limit N (s(u, v)) hp hp1 hq
    have hfreeR := fkgq_free_density_eq_limit (N + C + 1) ebA hp hp1 hq
    have hwiredL := fkgq_wired_density_eq_limit N (s(u, v)) hp hp1 hq
    have hwiredR := fkgq_wired_density_eq_limit (N + C + 1) ebA hp hp1 hq
    have hfreeSeq : ∀ k,
        edgeMargProb (fkProb (boxGraph d (N + k)) p q)
            (innerEdgeLE d (Nat.le_add_right N k) (s(u, v)))
          ≤ edgeMargProb (fkProb (boxGraph d ((N + C + 1) + k)) p q)
            (innerEdgeLE d (Nat.le_add_right (N + C + 1) k) ebA) := by
      intro k
      set m := N + k with hm
      set n := (N + C + 1) + k with hn
      have hsub : fvs_transBox d m a ⊆ box d n := by
        intro x hx i
        exact le_trans (fkgq_transBox_subset_box_add (d := d) m a hx i) (by simp [n, m, C]; omega)
      set em : Sym2 (boxVerts d m) := innerEdgeLE d (Nat.le_add_right N k) (s(u, v)) with hem
      set eS : Sym2 (fvs_transBoxVerts d m a) := Sym2.map (fvs_transEquiv d m a) em with heS
      have htrans := (fvs_box_translation_edgeMarg d m a em (p := p) (q := q)).2
      have hdom := bdp_latticeFree_multiMass_dominated (Sin := fvs_transBox d m a)
        (Sout := box d n) (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
        hp hp1 hq ({eS} : Finset (Sym2 (fvs_transBoxVerts d m a)))
      rw [Finset.image_singleton, ← bdp_edgeMargProb_eq_med_singleton,
        ← bdp_edgeMargProb_eq_med_singleton] at hdom
      have hedge : ocd_innerEdge (flc_incl hsub) eS
          = innerEdgeLE d (Nat.le_add_right (N + C + 1) k) ebA := by
        apply Sym2.map.injective (Subtype.val_injective (p := fun y => y ∈ box d n))
        simp only [eS, em, innerEdgeLE, ocd_innerEdge, Sym2.map_map, Sym2.map_mk, ebA, n, m]
        congr
      rw [← hedge]
      exact htrans.symm.trans_le hdom
    have hwiredSeq : ∀ k, 1 ≤ N + k →
        edgeMargProb (wiredFkProb (boxGraph d ((N + C + 1) + k))
            (boxBoundary d ((N + C + 1) + k)) p q)
            (innerEdgeLE d (Nat.le_add_right (N + C + 1) k) ebA)
          ≤ edgeMargProb (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p q)
            (innerEdgeLE d (Nat.le_add_right N k) (s(u, v))) := by
      intro k hm1
      set m := N + k with hm
      set n := (N + C + 1) + k with hn
      have hsub : fvs_transBox d m a ⊆ box d n := by
        intro x hx i
        exact le_trans (fkgq_transBox_subset_box_add (d := d) m a hx i) (by simp [n, m, C]; omega)
      set em : Sym2 (boxVerts d m) := innerEdgeLE d (Nat.le_add_right N k) (s(u, v)) with hem
      set eS : Sym2 (fvs_transBoxVerts d m a) := Sym2.map (fvs_transEquiv d m a) em with heS
      have htrans := (fvs_box_translation_edgeMarg d m a em (p := p) (q := q)).1
      have hmargin : ∀ x : fvs_transBoxVerts d m a, ¬ boxBoundary d n (flc_incl hsub x) := by
        intro x hbd
        have hx : (x : Site d) ∈ box d (n - 1) := by
          intro i
          exact le_trans (fkgq_transBox_subset_box_add (d := d) m a x.2 i)
            (by simp [n, m, C]; omega)
        exact hbd.2 hx
      have hdom := ocd_latticeWired_multiMass_dominated (Sin := fvs_transBox d m a)
        (Sout := box d n) (flc_incl hsub) (flc_incl_val hsub) (flc_incl_injective hsub)
        (boxBoundary d n) (fvs_transBoxBoundary d m a) hmargin
        (flc_hbdryIn_transBox hm1 a) hp hp1 hq
        ({eS} : Finset (Sym2 (fvs_transBoxVerts d m a)))
      rw [Finset.image_singleton, ← bdp_edgeMargProb_eq_med_singleton,
        ← bdp_edgeMargProb_eq_med_singleton] at hdom
      have hedge : ocd_innerEdge (flc_incl hsub) eS
          = innerEdgeLE d (Nat.le_add_right (N + C + 1) k) ebA := by
        apply Sym2.map.injective (Subtype.val_injective (p := fun y => y ∈ box d n))
        simp only [eS, em, innerEdgeLE, ocd_innerEdge, Sym2.map_map, Sym2.map_mk, ebA, n, m]
        congr
      rw [← hedge]
      exact hdom.trans_eq htrans
    constructor
    · rw [← hInclA]
      exact le_of_tendsto_of_tendsto hfreeL hfreeR (Filter.Eventually.of_forall hfreeSeq)
    · rw [← hInclA]
      refine le_of_tendsto_of_tendsto hwiredR hwiredL ?_
      filter_upwards [eventually_ge_atTop 1] with k hk
      exact hwiredSeq k (by omega)


theorem fkgq_density_translation_inv (N : ℕ) (eb : Sym2 (boxVerts d N)) (a : Site d)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (edgeIncl d N eb) p
        = freeEdgeDensity d q (Sym2.map (fun x => x + a) (edgeIncl d N eb)) p
      ∧ wiredEdgeDensity d q (edgeIncl d N eb) p
        = wiredEdgeDensity d q (Sym2.map (fun x => x + a) (edgeIncl d N eb)) p := by
  obtain ⟨hf, hw⟩ := fkgq_density_translate_order N eb a hp hp1 hq
  
  induction eb with
  | h u v =>
    set C := Finset.univ.sup (fun i => (a i).natAbs)
    have hua : (u : Site d) + a ∈ box d (N + C + 1) := by
      intro i
      exact le_trans (le_trans (Int.natAbs_add_le _ _)
        (Nat.add_le_add (u.2 i) (Finset.le_sup (f := fun j => (a j).natAbs) (Finset.mem_univ i)))) (by omega)
    have hva : (v : Site d) + a ∈ box d (N + C + 1) := by
      intro i
      exact le_trans (le_trans (Int.natAbs_add_le _ _)
        (Nat.add_le_add (v.2 i) (Finset.le_sup (f := fun j => (a j).natAbs) (Finset.mem_univ i)))) (by omega)
    set ebA : Sym2 (boxVerts d (N + C + 1)) :=
      s((⟨(u : Site d) + a, hua⟩ : boxVerts d (N + C + 1)),
        (⟨(v : Site d) + a, hva⟩ : boxVerts d (N + C + 1)))
    obtain ⟨hfback, hwback⟩ :=
      fkgq_density_translate_order (d := d) (N + C + 1) ebA (-a) hp hp1 hq
    have hA : edgeIncl d (N + C + 1) ebA
        = Sym2.map (fun x => x + a) (edgeIncl d N (s(u, v))) := by
      simp [ebA, edgeIncl]
    have hback : Sym2.map (fun x => x + -a) (edgeIncl d (N + C + 1) ebA)
        = edgeIncl d N (s(u, v)) := by
      rw [hA]
      simp only [Sym2.map_map]
      change Sym2.map ((fun x => x + -a) ∘ fun x => x + a) (edgeIncl d N (s(u, v)))
        = Sym2.map id (edgeIncl d N (s(u, v)))
      apply Sym2.map_congr
      intro x _
      simp
    rw [hback] at hfback hwback
    rw [hA] at hfback hwback
    exact ⟨le_antisymm hf hfback, le_antisymm hwback hw⟩


theorem fkgq_free_density_boxSym_lattice (S : BoxSym d) (e : Sym2 (Site d))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (Sym2.map S.τ e) p = freeEdgeDensity d q e p := by
  induction e with
  | h x y =>
    let N := max (Finset.univ.sup (fun i => (x i).natAbs))
      (Finset.univ.sup (fun i => (y i).natAbs))
    have hxN : x ∈ box d N := fun i =>
      le_trans (rot_site_mem_box x i) (Nat.le_max_left _ _)
    have hyN : y ∈ box d N := fun i =>
      le_trans (rot_site_mem_box y i) (Nat.le_max_right _ _)
    let eb : Sym2 (boxVerts d N) := s((⟨x, hxN⟩ : boxVerts d N), (⟨y, hyN⟩ : boxVerts d N))
    have hincl : edgeIncl d N eb = s(x, y) := by simp [eb, edgeIncl]
    rw [← hincl, ← rot_lift_edgeIncl S N eb]
    exact (fkgq_free_density_boxSym S N eb hp hp1 hq).symm


theorem fkgq_wired_density_boxSym_lattice (S : BoxSym d) (e : Sym2 (Site d))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredEdgeDensity d q (Sym2.map S.τ e) p = wiredEdgeDensity d q e p := by
  induction e with
  | h x y =>
    let N := max (Finset.univ.sup (fun i => (x i).natAbs))
      (Finset.univ.sup (fun i => (y i).natAbs))
    have hxN : x ∈ box d N := fun i =>
      le_trans (rot_site_mem_box x i) (Nat.le_max_left _ _)
    have hyN : y ∈ box d N := fun i =>
      le_trans (rot_site_mem_box y i) (Nat.le_max_right _ _)
    let eb : Sym2 (boxVerts d N) := s((⟨x, hxN⟩ : boxVerts d N), (⟨y, hyN⟩ : boxVerts d N))
    have hincl : edgeIncl d N eb = s(x, y) := by simp [eb, edgeIncl]
    rw [← hincl, ← rot_lift_edgeIncl S N eb]
    exact (fkgq_wired_density_boxSym S N eb hp hp1 hq).symm


theorem fkgq_density_translation_inv_lattice (e : Sym2 (Site d)) (a : Site d)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q e p = freeEdgeDensity d q (Sym2.map (fun x => x + a) e) p ∧
      wiredEdgeDensity d q e p = wiredEdgeDensity d q (Sym2.map (fun x => x + a) e) p := by
  induction e with
  | h x y =>
    let N := max (Finset.univ.sup (fun i => (x i).natAbs))
      (Finset.univ.sup (fun i => (y i).natAbs))
    have hxN : x ∈ box d N := fun i =>
      le_trans (rot_site_mem_box x i) (Nat.le_max_left _ _)
    have hyN : y ∈ box d N := fun i =>
      le_trans (rot_site_mem_box y i) (Nat.le_max_right _ _)
    let eb : Sym2 (boxVerts d N) := s((⟨x, hxN⟩ : boxVerts d N), (⟨y, hyN⟩ : boxVerts d N))
    have hincl : edgeIncl d N eb = s(x, y) := by simp [eb, edgeIncl]
    simpa [hincl] using fkgq_density_translation_inv (d := d) N eb a hp hp1 hq


theorem fkgq_free_density_recentre (x y : Site d) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (s(x, y) : Sym2 (Site d)) p
      = freeEdgeDensity d q (s((0 : Site d), y - x) : Sym2 (Site d)) p := by
  have h := (fkgq_density_translation_inv_lattice
    (d := d) (s(x, y) : Sym2 (Site d)) (-x) hp hp1 hq).1
  rw [h]
  congr 1
  simp only [Sym2.map_mk]
  congr <;> simp


theorem fkgq_wired_density_recentre (x y : Site d) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredEdgeDensity d q (s(x, y) : Sym2 (Site d)) p
      = wiredEdgeDensity d q (s((0 : Site d), y - x) : Sym2 (Site d)) p := by
  have h := (fkgq_density_translation_inv_lattice
    (d := d) (s(x, y) : Sym2 (Site d)) (-x) hp hp1 hq).2
  rw [h]
  congr 1
  simp only [Sym2.map_mk]
  congr <;> simp


theorem fkgq_free_centred_unit_const (hd : 0 < d) (j : Fin d) (b : Bool) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = freeEdgeDensity d q (rot_refUnitEdge d hd) p := by
  have hpos : freeEdgeDensity d q
      (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = freeEdgeDensity d q
          (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) p := by
    cases b with
    | true => rfl
    | false =>
        rw [← fkgq_free_density_boxSym_lattice (fkTI_signFlip d j)
              (s((0 : Site d), candMap d (0 : Site d) (j, false)) : Sym2 (Site d)) hp hp1 hq,
            rot_map_centred_edge, rot_signFlip_neg_to_pos]
  rw [hpos, ← fkgq_free_density_boxSym_lattice
        (rot_permBoxSym d (Equiv.swap (⟨0, hd⟩ : Fin d) j))
        (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) hp hp1 hq,
      rot_map_centred_edge]
  show freeEdgeDensity d q (s((0 : Site d),
      rot_permEquiv d (Equiv.swap (⟨0, hd⟩ : Fin d) j)
        (candMap d (0 : Site d) (j, true)))) p = _
  rw [rot_permEquiv_axis_to_zero j hd]
  rfl


theorem fkgq_wired_centred_unit_const (hd : 0 < d) (j : Fin d) (b : Bool) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredEdgeDensity d q (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = wiredEdgeDensity d q (rot_refUnitEdge d hd) p := by
  have hpos : wiredEdgeDensity d q
      (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p
      = wiredEdgeDensity d q
          (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) p := by
    cases b with
    | true => rfl
    | false =>
        rw [← fkgq_wired_density_boxSym_lattice (fkTI_signFlip d j)
              (s((0 : Site d), candMap d (0 : Site d) (j, false)) : Sym2 (Site d)) hp hp1 hq,
            rot_map_centred_edge, rot_signFlip_neg_to_pos]
  rw [hpos, ← fkgq_wired_density_boxSym_lattice
        (rot_permBoxSym d (Equiv.swap (⟨0, hd⟩ : Fin d) j))
        (s((0 : Site d), candMap d (0 : Site d) (j, true)) : Sym2 (Site d)) hp hp1 hq,
      rot_map_centred_edge]
  show wiredEdgeDensity d q (s((0 : Site d),
      rot_permEquiv d (Equiv.swap (⟨0, hd⟩ : Fin d) j)
        (candMap d (0 : Site d) (j, true)))) p = _
  rw [rot_permEquiv_axis_to_zero j hd]
  rfl


theorem fkgq_free_edge_const (hd : 0 < d) (x y : Site d)
    (hadj : (hypercubicLattice d).Adj x y) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (s(x, y) : Sym2 (Site d)) p
      = freeEdgeDensity d q (rot_refUnitEdge d hd) p := by
  obtain ⟨⟨j, b⟩, hdir⟩ := rot_edge_dir x y hadj
  rw [fkgq_free_density_recentre x y hp hp1 hq, hdir]
  exact fkgq_free_centred_unit_const hd j b hp hp1 hq


theorem fkgq_wired_edge_const (hd : 0 < d) (x y : Site d)
    (hadj : (hypercubicLattice d).Adj x y) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredEdgeDensity d q (s(x, y) : Sym2 (Site d)) p
      = wiredEdgeDensity d q (rot_refUnitEdge d hd) p := by
  obtain ⟨⟨j, b⟩, hdir⟩ := rot_edge_dir x y hadj
  rw [fkgq_wired_density_recentre x y hp hp1 hq, hdir]
  exact fkgq_wired_centred_unit_const hd j b hp hp1 hq


theorem fkgq_free_box_edge_const (hd : 0 < d) (m : ℕ) (eb : Sym2 (boxVerts d m))
    (heb : eb ∈ (boxGraph d m).edgeFinset) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (edgeIncl d m eb) p
      = freeEdgeDensity d q (rot_refUnitEdge d hd) p := by
  rw [SimpleGraph.mem_edgeFinset] at heb
  induction eb with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet, boxGraph, SimpleGraph.comap_adj] at heb
    exact fkgq_free_edge_const hd (u : Site d) (v : Site d) heb hp hp1 hq


theorem fkgq_wired_box_edge_const (hd : 0 < d) (m : ℕ) (eb : Sym2 (boxVerts d m))
    (heb : eb ∈ (boxGraph d m).edgeFinset) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredEdgeDensity d q (edgeIncl d m eb) p
      = wiredEdgeDensity d q (rot_refUnitEdge d hd) p := by
  rw [SimpleGraph.mem_edgeFinset] at heb
  induction eb with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet, boxGraph, SimpleGraph.comap_adj] at heb
    exact fkgq_wired_edge_const hd (u : Site d) (v : Site d) heb hp hp1 hq


theorem fkgq_fkExpect_openCount_eq_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p q : ℝ) :
    fkExpect G p q (fun ω => (openCount G ω : ℝ))
      = ∑ e ∈ G.edgeFinset, edgeMargProb (fkProb G p q) e := by
  unfold fkExpect
  rw [show (fun ω => fkProb G p q ω * (openCount G ω : ℝ))
      = (fun ω => dfi_openEdgeCount G.edgeFinset ω * fkProb G p q ω) from ?_]
  · exact dfi_openEdgeCount_expect G.edgeFinset (fkProb G p q)
  · funext ω
    rw [adc_openCount_eq_sum]
    ring


theorem fkgq_avgDensity_eq_sum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q t : ℝ) :
    fkgq_avgDensity G q t = (1 / (G.edgeFinset.card : ℝ))
      * ∑ e ∈ G.edgeFinset, edgeMargProb (fkProb G (fsc_logistic t) q) e := by
  unfold fkgq_avgDensity
  rw [fkgq_fkExpect_openCount_eq_sum]


theorem fkgq_free_avg_collapse (q t : ℝ) (hq : 1 ≤ q)
    (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (In : (n : ℕ) → Finset (Sym2 (boxVerts d n)))
    (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (nhds 0))
    (hin : ∀ n, ∀ e ∈ In n,
      |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) q) e - L| ≤ δ n)
    (hbdy : Tendsto (fun n =>
      (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
      atTop (nhds 0)) :
    Tendsto (fun n => fkgq_avgDensity (boxGraph d n) q t) atTop (nhds L) := by
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  rw [show (fun n => fkgq_avgDensity (boxGraph d n) q t) = fun n =>
      (1 / ((boxGraph d n).edgeFinset.card : ℝ)) * ∑ e ∈ (boxGraph d n).edgeFinset,
        edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) q) e from
    funext fun n => fkgq_avgDensity_eq_sum (boxGraph d n) q t]
  exact adc_absavg_tendsto
    (En := fun n => (boxGraph d n).edgeFinset) In
    (fn := fun n e => edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) q) e)
    L δ hIE
    (fun n e _ => adc_edgeMargProb_fkProb_nonneg (boxGraph d n) hp hp1
      (zero_lt_one.trans_le hq) e)
    (fun n e _ => adc_edgeMargProb_fkProb_le_one (boxGraph d n) hp hp1
      (zero_lt_one.trans_le hq) e)
    hL0 hL1 hδ0 hδlim hin hE hbdy


theorem fkgq_wired_avg_collapse (q t : ℝ) (hq : 1 ≤ q)
    (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (In : (n : ℕ) → Finset (Sym2 (boxVerts d n)))
    (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (nhds 0))
    (hin : ∀ n, ∀ e ∈ In n,
      |edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) q) e - L|
        ≤ δ n)
    (hbdy : Tendsto (fun n =>
      (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
      atTop (nhds 0)) :
    Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) q t)
      atTop (nhds L) := by
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  rw [show (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) q t) = fun n =>
      (1 / ((boxGraph d n).edgeFinset.card : ℝ)) * ∑ e ∈ (boxGraph d n).edgeFinset,
        edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) q) e from
    funext fun n => wpd_avgWiredDensity_eq_sum_edgeMarg
      (boxGraph d n) (boxBoundary d n) q t]
  exact adc_absavg_tendsto
    (En := fun n => (boxGraph d n).edgeFinset) In
    (fn := fun n e => edgeMargProb
      (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) q) e)
    L δ hIE
    (fun n e _ => ubd_edgeMargProb_wiredFkProb_nonneg (boxGraph d n) (boxBoundary d n)
      hp hp1 (zero_lt_one.trans_le hq) e)
    (fun n e _ => ubd_edgeMargProb_wiredFkProb_le_one (boxGraph d n) (boxBoundary d n)
      hp hp1 (zero_lt_one.trans_le hq) e)
    hL0 hL1 hδ0 hδlim hin hE hbdy


end StatMech.FK
