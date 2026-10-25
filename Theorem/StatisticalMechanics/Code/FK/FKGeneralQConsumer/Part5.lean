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
import Def.StatisticalMechanics.Code.FK.FKGeneralQConsumer.Part4
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


theorem fkgq_freeDelta_nonneg (N : ℕ) (e : Sym2 (boxVerts d N)) (q t : ℝ) (n : ℕ) :
    0 ≤ fkgq_freeDelta N e q t n := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem fkgq_wiredDelta_nonneg (N : ℕ) (e : Sym2 (boxVerts d N)) (q t : ℝ) (n : ℕ) :
    0 ≤ fkgq_wiredDelta N e q t n := Finset.sum_nonneg fun _ _ => abs_nonneg _


theorem fkgq_freeDelta_tendsto_zero (hd : 1 ≤ d) (N : ℕ) (e : Sym2 (boxVerts d N))
    (he : e ∈ (boxGraph d N).edgeFinset) (q : ℝ) (hq : 1 ≤ q) (t : ℝ) :
    Tendsto (fun n => fkgq_freeDelta N e q t n) atTop (nhds 0) := by
  have hdir : ∀ dir : Fin d × Bool,
      freeEdgeDensity d q (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) dir)) (fsc_logistic t)
        = freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) := by
    intro dir
    exact (fkgq_free_box_edge_const (lt_of_lt_of_le one_pos hd) 1 _
      (ocs_unitEdge1_mem_edgeFinset d dir) (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq).trans
      (fkgq_free_box_edge_const (lt_of_lt_of_le one_pos hd) N e he
        (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq).symm
  unfold fkgq_freeDelta
  convert tendsto_finset_sum Finset.univ (fun dir _ =>
    (((tendsto_const_nhds.sub (fkgq_unitMarg_tendsto q hq dir t)).abs).congr'
      (Filter.Eventually.of_forall fun n => rfl))) using 1 <;> simp [hdir]


theorem fkgq_wiredDelta_tendsto_zero (hd : 1 ≤ d) (N : ℕ) (e : Sym2 (boxVerts d N))
    (he : e ∈ (boxGraph d N).edgeFinset) (q : ℝ) (hq : 1 ≤ q) (t : ℝ) :
    Tendsto (fun n => fkgq_wiredDelta N e q t n) atTop (nhds 0) := by
  have hdir : ∀ dir : Fin d × Bool,
      wiredEdgeDensity d q (edgeIncl d 1 (ocs_unitEdge d 1 (le_refl 1) dir)) (fsc_logistic t)
        = wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) := by
    intro dir
    exact (fkgq_wired_box_edge_const (lt_of_lt_of_le one_pos hd) 1 _
      (ocs_unitEdge1_mem_edgeFinset d dir) (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq).trans
      (fkgq_wired_box_edge_const (lt_of_lt_of_le one_pos hd) N e he
        (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq).symm
  unfold fkgq_wiredDelta
  convert tendsto_finset_sum Finset.univ (fun dir _ =>
    (((fkgq_unitWiredMarg_tendsto q hq dir t).sub tendsto_const_nhds).abs.congr'
      (Filter.Eventually.of_forall fun n => rfl))) using 1 <;> simp [hdir]


theorem fkgq_freeDensity_mem_Icc (N : ℕ) (e : Sym2 (boxVerts d N))
    (q : ℝ) (hq : 1 ≤ q) (t : ℝ) :
    freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) ∈ Set.Icc (0 : ℝ) 1 := by
  have hlim := fkgq_free_density_eq_limit (d := d) N e
    (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq
  constructor
  · exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
      adc_edgeMargProb_fkProb_nonneg (boxGraph d (N + k))
        (fsc_logistic_pos t) (fsc_logistic_lt_one t) (zero_lt_one.trans_le hq)
        (innerEdgeLE d (Nat.le_add_right N k) e))
  · exact le_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
      adc_edgeMargProb_fkProb_le_one (boxGraph d (N + k))
        (fsc_logistic_pos t) (fsc_logistic_lt_one t) (zero_lt_one.trans_le hq)
        (innerEdgeLE d (Nat.le_add_right N k) e))


theorem fkgq_wiredDensity_mem_Icc (N : ℕ) (e : Sym2 (boxVerts d N))
    (q : ℝ) (hq : 1 ≤ q) (t : ℝ) :
    wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) ∈ Set.Icc (0 : ℝ) 1 := by
  have hlim := fkgq_wired_density_eq_limit (d := d) N e
    (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq
  constructor
  · exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
      ubd_edgeMargProb_wiredFkProb_nonneg (boxGraph d (N + k))
        (boxBoundary d (N + k)) (fsc_logistic_pos t) (fsc_logistic_lt_one t)
        (zero_lt_one.trans_le hq) (innerEdgeLE d (Nat.le_add_right N k) e))
  · exact le_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
      ubd_edgeMargProb_wiredFkProb_le_one (boxGraph d (N + k))
        (boxBoundary d (N + k)) (fsc_logistic_pos t) (fsc_logistic_lt_one t)
        (zero_lt_one.trans_le hq) (innerEdgeLE d (Nat.le_add_right N k) e))

set_option maxHeartbeats 2000000 in

theorem fkgq_free_bulk_lower (N : ℕ) (e : Sym2 (boxVerts d N))
    (q : ℝ) (hq : 1 ≤ q) (t : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (u v : boxVerts d (n - Nat.sqrt n))
    (hadj : (boxGraph d (n - Nat.sqrt n)).Adj u v) :
    freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) - fkgq_freeDelta N e q t n
      ≤ edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) q)
        (innerEdgeLE d (Nat.sub_le n (Nat.sqrt n))
          (s(u, v) : Sym2 (boxVerts d (n - Nat.sqrt n)))) := by
  have hR : 1 ≤ Nat.sqrt n := by
    rw [Nat.one_le_iff_ne_zero, Ne, Nat.sqrt_eq_zero]
    omega
  obtain ⟨dir, hdir⟩ := ocs_edge_dir_candMap d (n - Nat.sqrt n) u v hadj
  have c0 := ocs_zero_mem_box d (Nat.sqrt n)
  have cw : ((v : Site d) - (u : Site d)) ∈ box d (Nat.sqrt n) := by
    rw [hdir]
    exact ocs_candMap_mem_box d (Nat.sqrt n) hR dir
  have hlow := fkgq_free_offCentre_lower (d := d) (Nat.sqrt n) n
    (Nat.sqrt_le_self n) (Nat.sub_le n (Nat.sqrt n)) u v
    (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq c0 cw
  have hue : (s((⟨(0 : Site d), c0⟩ : boxVerts d (Nat.sqrt n)),
      (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d (Nat.sqrt n)))) =
      ocs_unitEdge d (Nat.sqrt n) hR dir := by
    unfold ocs_unitEdge
    congr 1
    exact Subtype.ext hdir
  rw [hue] at hlow
  have hmarg : fkgq_unitMarg d q n dir t = edgeMargProb
      (fkProb (boxGraph d (Nat.sqrt n)) (fsc_logistic t) q)
      (ocs_unitEdge d (Nat.sqrt n) hR dir) := by
    unfold fkgq_unitMarg
    rw [dif_pos hR]
  have hterm : |freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) -
      fkgq_unitMarg d q n dir t| ≤ fkgq_freeDelta N e q t n :=
    Finset.single_le_sum (fun x _ => abs_nonneg
      (freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) -
        fkgq_unitMarg d q n x t)) (Finset.mem_univ dir)
  have h1 : freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) -
      fkgq_freeDelta N e q t n ≤ fkgq_unitMarg d q n dir t := by
    have := (le_abs_self (freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) -
      fkgq_unitMarg d q n dir t)).trans hterm
    linarith
  rw [hmarg] at h1
  exact h1.trans hlow

set_option maxHeartbeats 2000000 in

theorem fkgq_wired_bulk_upper (N : ℕ) (e : Sym2 (boxVerts d N))
    (q : ℝ) (hq : 1 ≤ q) (t : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (u v : boxVerts d (n - Nat.sqrt n - 1))
    (hadj : (boxGraph d (n - Nat.sqrt n - 1)).Adj u v) :
    edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) q)
        (innerEdgeLE d (Nat.sub_le (n - Nat.sqrt n) 1 |>.trans
          (Nat.sub_le n (Nat.sqrt n)))
          (s(u, v) : Sym2 (boxVerts d (n - Nat.sqrt n - 1))))
      ≤ wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) +
        fkgq_wiredDelta N e q t n := by
  have hR : 1 ≤ Nat.sqrt n := by
    rw [Nat.one_le_iff_ne_zero, Ne, Nat.sqrt_eq_zero]
    omega
  have hRn1 : Nat.sqrt n + 1 ≤ n := by
    have h2 : Nat.sqrt n * Nat.sqrt n ≤ n := by
      simpa [pow_two] using Nat.sqrt_le' n
    nlinarith [Nat.sqrt_le_self n, h2]
  let hmn := Nat.sub_le (n - Nat.sqrt n) 1 |>.trans (Nat.sub_le n (Nat.sqrt n))
  obtain ⟨dir, hdir⟩ := ocs_edge_dir_candMap d (n - Nat.sqrt n - 1) u v hadj
  have c0 := ocs_zero_mem_box d (Nat.sqrt n)
  have cw : ((v : Site d) - (u : Site d)) ∈ box d (Nat.sqrt n) := by
    rw [hdir]
    exact ocs_candMap_mem_box d (Nat.sqrt n) hR dir
  have hup := fkgq_wired_offCentre_upper (d := d) (Nat.sqrt n) n hR hRn1 hmn u v
    (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq c0 cw
  have hue : (s((⟨(0 : Site d), c0⟩ : boxVerts d (Nat.sqrt n)),
      (⟨(v : Site d) - (u : Site d), cw⟩ : boxVerts d (Nat.sqrt n)))) =
      ocs_unitEdge d (Nat.sqrt n) hR dir := by
    unfold ocs_unitEdge
    congr 1
    exact Subtype.ext hdir
  rw [hue] at hup
  have hmarg : fkgq_unitWiredMarg d q n dir t = edgeMargProb
      (wiredFkProb (boxGraph d (Nat.sqrt n)) (boxBoundary d (Nat.sqrt n))
        (fsc_logistic t) q) (ocs_unitEdge d (Nat.sqrt n) hR dir) := by
    unfold fkgq_unitWiredMarg
    rw [dif_pos hR]
  have hterm : |fkgq_unitWiredMarg d q n dir t -
      wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t)| ≤
      fkgq_wiredDelta N e q t n :=
    Finset.single_le_sum (fun x _ => abs_nonneg
      (fkgq_unitWiredMarg d q n x t -
        wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t)))
      (Finset.mem_univ dir)
  have h1 : fkgq_unitWiredMarg d q n dir t ≤
      wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) +
        fkgq_wiredDelta N e q t n := by
    have := (le_abs_self (fkgq_unitWiredMarg d q n dir t -
      wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t))).trans hterm
    linarith
  rw [hmarg] at h1
  exact hup.trans h1


theorem fkgq_genuineFreeCollapse (hd : 1 ≤ d) (N : ℕ)
    (e : Sym2 (boxVerts d N)) (he : e ∈ (boxGraph d N).edgeFinset)
    (q : ℝ) (hq : 1 ≤ q) (t : ℝ) :
    Tendsto (fun n => fkgq_avgDensity (boxGraph d n) q t) atTop
      (nhds (freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t))) := by
  let L := freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t)
  obtain ⟨hL0, hL1⟩ := fkgq_freeDensity_mem_Icc N e q hq t
  let In := ocs_bulkSet d
  let δ := fkgq_freeDelta N e q t
  apply fkgq_freeBulkCollapse_n1 q t (zero_lt_one.trans_le hq)
    (fun n hn => ecz_box_edge_pos d hd hn) L hL0 hL1 In
  · intro n x hx
    change x ∈ ocs_bulkSet d n at hx
    rw [ocs_bulkSet, Finset.mem_image] at hx
    obtain ⟨eb, heb, rfl⟩ := hx
    exact ocs_innerEdgeLE_mem_edgeFinset d _ eb heb
  · exact fun n => fkgq_freeDelta_nonneg N e q t n
  · exact fkgq_freeDelta_tendsto_zero hd N e he q hq t
  · intro n x hx
    change x ∈ ocs_bulkSet d n at hx
    rw [ocs_bulkSet, Finset.mem_image] at hx
    obtain ⟨eb, heb, rfl⟩ := hx
    rw [SimpleGraph.mem_edgeFinset] at heb
    have hupper : edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) q)
        (innerEdgeLE d (Nat.sub_le n (Nat.sqrt n)) eb) ≤ L := by
      refine (fkgq_free_per_edge_upper n _ (fsc_logistic_pos t)
        (fsc_logistic_lt_one t) hq).trans_eq ?_
      rw [edgeIncl_innerEdgeLE]
      calc
        freeEdgeDensity d q (edgeIncl d (n - Nat.sqrt n) eb) (fsc_logistic t)
            = freeEdgeDensity d q (rot_refUnitEdge d (lt_of_lt_of_le one_pos hd))
                (fsc_logistic t) :=
          fkgq_free_box_edge_const (lt_of_lt_of_le one_pos hd) _ eb
            (by simpa [SimpleGraph.mem_edgeFinset] using heb)
            (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq
        _ = L := by
          dsimp [L]
          exact (fkgq_free_box_edge_const (lt_of_lt_of_le one_pos hd) N e he
            (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq).symm
    have hlower : L - δ n ≤ edgeMargProb
        (fkProb (boxGraph d n) (fsc_logistic t) q)
        (innerEdgeLE d (Nat.sub_le n (Nat.sqrt n)) eb) := by
      by_cases hn : 1 ≤ n
      · induction eb with
        | h u v =>
          rw [SimpleGraph.mem_edgeSet] at heb
          exact fkgq_free_bulk_lower N e q hq t n hn u v heb
      · exfalso
        have hn0 : n = 0 := by omega
        subst n
        induction eb with
        | h u v =>
          rw [SimpleGraph.mem_edgeSet] at heb
          have huv : (u : Site d) = (v : Site d) := by
            funext i
            have hu := u.2 i
            have hv := v.2 i
            simp only [Nat.zero_sub, mem_box] at hu hv
            omega
          rw [boxGraph, SimpleGraph.comap_adj, huv] at heb
          simpa [NearestNeighbour] using heb
    rw [abs_le]
    constructor <;> linarith [fkgq_freeDelta_nonneg N e q t n]
  · have hcard : ∀ n, (In n).card =
        (boxGraph d (n - Nat.sqrt n)).edgeFinset.card := fun n =>
      Finset.card_image_of_injective _
        (dfi_innerEdgeLE_injective d (Nat.sub_le n (Nat.sqrt n)))
    refine (ocs_edgeFinset_shell_fraction_tendsto_zero d hd
      (fun n => n - Nat.sqrt n) (fun n => Nat.sub_le n _)
      ocs_gap_sub_tendsto_zero).congr (fun n => ?_)
    rw [hcard n]


theorem fkgq_genuineWiredCollapse (hd : 1 ≤ d) (N : ℕ)
    (e : Sym2 (boxVerts d N)) (he : e ∈ (boxGraph d N).edgeFinset)
    (q : ℝ) (hq : 1 ≤ q) (t : ℝ) :
    Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) q t) atTop
      (nhds (wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t))) := by
  let L := wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t)
  obtain ⟨hL0, hL1⟩ := fkgq_wiredDensity_mem_Icc N e q hq t
  let In := ocs_wiredBulkSet d
  let δ := fkgq_wiredDelta N e q t
  apply fkgq_wiredBulkCollapse_n1 q t (zero_lt_one.trans_le hq)
    (fun n hn => ecz_box_edge_pos d hd hn) L hL0 hL1 In
  · intro n x hx
    change x ∈ ocs_wiredBulkSet d n at hx
    rw [ocs_wiredBulkSet, Finset.mem_image] at hx
    obtain ⟨eb, heb, rfl⟩ := hx
    exact ocs_innerEdgeLE_mem_edgeFinset d _ eb heb
  · exact fun n => fkgq_wiredDelta_nonneg N e q t n
  · exact fkgq_wiredDelta_tendsto_zero hd N e he q hq t
  · intro n x hx
    change x ∈ ocs_wiredBulkSet d n at hx
    rw [ocs_wiredBulkSet, Finset.mem_image] at hx
    obtain ⟨eb, heb, rfl⟩ := hx
    rw [SimpleGraph.mem_edgeFinset] at heb
    let hmn := Nat.sub_le (n - Nat.sqrt n) 1 |>.trans (Nat.sub_le n (Nat.sqrt n))
    have hlower : L ≤ edgeMargProb
        (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) q)
        (innerEdgeLE d hmn eb) := by
      have hconst : L = wiredEdgeDensity d q (edgeIncl d (n - Nat.sqrt n - 1) eb)
          (fsc_logistic t) := by
        dsimp [L]
        calc
          wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t)
              = wiredEdgeDensity d q (rot_refUnitEdge d (lt_of_lt_of_le one_pos hd))
                  (fsc_logistic t) :=
            fkgq_wired_box_edge_const (lt_of_lt_of_le one_pos hd) N e he
              (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq
          _ = wiredEdgeDensity d q (edgeIncl d (n - Nat.sqrt n - 1) eb)
                (fsc_logistic t) :=
            (fkgq_wired_box_edge_const (lt_of_lt_of_le one_pos hd) _ eb
              (by simpa [SimpleGraph.mem_edgeFinset] using heb)
              (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq).symm
      rw [hconst]
      rw [← edgeIncl_innerEdgeLE]
      exact fkgq_wired_per_edge_lower n _ (fsc_logistic_pos t)
        (fsc_logistic_lt_one t) hq
    have hupper : edgeMargProb
        (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) q)
        (innerEdgeLE d hmn eb) ≤ L + δ n := by
      by_cases hn : 2 ≤ n
      · induction eb with
        | h u v =>
          rw [SimpleGraph.mem_edgeSet] at heb
          exact fkgq_wired_bulk_upper N e q hq t n hn u v heb
      · exfalso
        have hzero : n - Nat.sqrt n - 1 = 0 := by
          interval_cases n <;> simp [Nat.sqrt]
        induction eb with
        | h u v =>
          rw [SimpleGraph.mem_edgeSet] at heb
          have huv : (u : Site d) = (v : Site d) := by
            funext i
            have hu := u.2 i
            have hv := v.2 i
            simp only [mem_box, hzero] at hu hv
            omega
          rw [boxGraph, SimpleGraph.comap_adj, huv] at heb
          simpa [NearestNeighbour] using heb
    rw [abs_le]
    constructor <;> linarith [fkgq_wiredDelta_nonneg N e q t n]
  · have hcard : ∀ n, (In n).card =
        (boxGraph d (n - Nat.sqrt n - 1)).edgeFinset.card := fun n =>
      Finset.card_image_of_injective _ (dfi_innerEdgeLE_injective d _)
    refine (ocs_edgeFinset_shell_fraction_tendsto_zero d hd
      (fun n => n - Nat.sqrt n - 1)
      (fun n => Nat.sub_le (n - Nat.sqrt n) 1 |>.trans (Nat.sub_le n (Nat.sqrt n)))
      ocs_gap_sub_one_tendsto_zero).congr (fun n => ?_)
    rw [hcard n]


theorem fkgq_free_density_nonEdge (N : ℕ) (e : Sym2 (boxVerts d N))
    (he : e ∉ (boxGraph d N).edgeFinset) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (edgeIncl d N e) p = 1 / 2 := by
  have hlim := fkgq_free_density_eq_limit (d := d) N e hp hp1 hq
  have hconst : (fun k => edgeMargProb (fkProb (boxGraph d (N + k)) p q)
      (innerEdgeLE d (Nat.le_add_right N k) e)) = fun _ => (1 / 2 : ℝ) := by
    funext k
    apply fpe2_edgeMargProb_half_of_toggle_invariant
    · exact fkProb_sum_eq_one (boxGraph d (N + k)) hp hp1 (zero_lt_one.trans_le hq)
    · intro ω
      exact fpe2_fkProb_toggle_invariant (boxGraph d (N + k))
        (fpe2_innerEdgeLE_notMem_edgeFinset N (N + k) (Nat.le_add_right N k) e he) ω
  rw [hconst] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm


theorem fkgq_wired_density_nonEdge (N : ℕ) (e : Sym2 (boxVerts d N))
    (he : e ∉ (boxGraph d N).edgeFinset) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    wiredEdgeDensity d q (edgeIncl d N e) p = 1 / 2 := by
  have hlim := fkgq_wired_density_eq_limit (d := d) N e hp hp1 hq
  have hconst : (fun k => edgeMargProb
      (wiredFkProb (boxGraph d (N + k)) (boxBoundary d (N + k)) p q)
      (innerEdgeLE d (Nat.le_add_right N k) e)) = fun _ => (1 / 2 : ℝ) := by
    funext k
    apply fpe2_edgeMargProb_half_of_toggle_invariant
    · exact wiredFkProb_sum_eq_one (boxGraph d (N + k)) (boxBoundary d (N + k))
        hp hp1 (zero_lt_one.trans_le hq)
    · intro ω
      exact fpe2_wiredFkProb_toggle_invariant (boxGraph d (N + k))
        (boxBoundary d (N + k))
        (fpe2_innerEdgeLE_notMem_edgeFinset N (N + k) (Nat.le_add_right N k) e he) ω
  rw [hconst] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm


theorem fkgq_free_density_le_wired (N : ℕ) (e : Sym2 (boxVerts d N))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    freeEdgeDensity d q (edgeIncl d N e) p ≤
      wiredEdgeDensity d q (edgeIncl d N e) p := by
  have h := fkgq_freeIV_le_wiredIV d N hp hp1 hq
    (boxEdgeOpenEvent_isIncreasing d N e)
  unfold freeEdgeDensity wiredEdgeDensity
  rw [dif_pos ⟨hp, hp1, zero_lt_one.trans_le hq⟩,
    dif_pos ⟨hp, hp1, zero_lt_one.trans_le hq⟩]
  exact h


theorem fkgq_centered_deriv_eq_densities (hd : 1 ≤ d) (q : ℝ) (hq : 1 ≤ q)
    {G : ℝ → ℝ} (hG : ConvexOn ℝ Set.univ G)
    (hlim : ∀ s, Tendsto (fun n => cfe_centered (boxGraph d n) q s) atTop (nhds (G s)))
    (N : ℕ) (e : Sym2 (boxVerts d N)) (he : e ∈ (boxGraph d N).edgeFinset)
    (t : ℝ) (hdiff : pressureLeftDeriv G t = pressureRightDeriv G t) :
    freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) = pressureLeftDeriv G t ∧
      wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) = pressureRightDeriv G t := by
  have hbox1 : ∀ n, 1 ≤ n → 0 < (boxGraph d n).edgeFinset.card :=
    fun n hn => ecz_box_edge_pos d hd hn
  have hshift : ∀ s, Tendsto (fun n => cfe_centered (boxGraph d (n + 1)) q s)
      atTop (nhds (G s)) := fun s => (hlim s).comp (tendsto_add_atTop_nat 1)
  have hfreeCol : Tendsto (fun n => fkgq_avgDensity (boxGraph d n) q t) atTop
      (nhds (freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t))) :=
    fkgq_genuineFreeCollapse hd N e he q hq t
  have hwiredCol : Tendsto
      (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) q t) atTop
      (nhds (wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t))) :=
    fkgq_genuineWiredCollapse hd N e he q hq t
  have hfreeShift := hfreeCol.comp (tendsto_add_atTop_nat 1)
  have hwiredShift := hwiredCol.comp (tendsto_add_atTop_nat 1)
  have hfreeL : pressureLeftDeriv G t ≤
      freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) :=
    fdd_leftDeriv_le_avgLimit
      (fun n => cfe_centered (boxGraph d (n + 1)) q) G
      (fun n => fkgq_avgDensity (boxGraph d (n + 1)) q)
      (fun n => cfe_centered_convexOn (boxGraph d (n + 1)) q
        (zero_lt_one.trans_le hq) (hbox1 (n + 1) (by omega)))
      (fun n s => fkgq_centered_hasDerivAt (boxGraph d (n + 1)) q
        (zero_lt_one.trans_le hq) (hbox1 (n + 1) (by omega)) s)
      hshift t _ hG hfreeShift
  have hfreeR : freeEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) ≤
      pressureRightDeriv G t :=
    fdd_avgLimit_le_rightDeriv
      (fun n => cfe_centered (boxGraph d (n + 1)) q) G
      (fun n => fkgq_avgDensity (boxGraph d (n + 1)) q)
      (fun n => cfe_centered_convexOn (boxGraph d (n + 1)) q
        (zero_lt_one.trans_le hq) (hbox1 (n + 1) (by omega)))
      (fun n s => fkgq_centered_hasDerivAt (boxGraph d (n + 1)) q
        (zero_lt_one.trans_le hq) (hbox1 (n + 1) (by omega)) s)
      hshift t _ hG hfreeShift
  have hwlim : ∀ s, Tendsto (fun n => cfe_wiredCentered (boxGraph d (n + 1))
      (boxBoundary d (n + 1)) q s) atTop (nhds (G s)) := fun s =>
    (fkgq_wiredCentered_tendsto d hd q hq s (hlim s)).comp (tendsto_add_atTop_nat 1)
  have hwiredR : wiredEdgeDensity d q (edgeIncl d N e) (fsc_logistic t) ≤
      pressureRightDeriv G t :=
    fdd_avgLimit_le_rightDeriv
      (fun n => cfe_wiredCentered (boxGraph d (n + 1)) (boxBoundary d (n + 1)) q) G
      (fun n => wpd_avgWiredDensity (boxGraph d (n + 1)) (boxBoundary d (n + 1)) q)
      (fun n => cfe_wiredCentered_convexOn (boxGraph d (n + 1))
        (boxBoundary d (n + 1)) q (zero_lt_one.trans_le hq)
        (hbox1 (n + 1) (by omega)))
      (fun n s => fkgq_wiredCentered_hasDerivAt (boxGraph d (n + 1))
        (boxBoundary d (n + 1)) q (zero_lt_one.trans_le hq)
        (hbox1 (n + 1) (by omega)) s)
      hwlim t _ hG hwiredShift
  have hfw := fkgq_free_density_le_wired N e
    (fsc_logistic_pos t) (fsc_logistic_lt_one t) hq
  constructor
  · apply le_antisymm
    · exact hfreeR.trans_eq hdiff.symm
    · exact hfreeL
  · apply le_antisymm hwiredR
    rw [← hdiff]
    exact hfreeL.trans hfw


theorem fkgq_countable_free_wired_disagreement (hd : 1 ≤ d) (N : ℕ)
    (q : ℝ) (hq : 1 ≤ q) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
      eventMassProb (fkgq_freeMass d N q hq t) A ≠
        eventMassProb (fkgq_wiredMass d N q hq t) A}.Countable := by
  obtain ⟨G, hlim, hG, _⟩ := fkgq_centeredConvergence d hd q hq
  refine (countable_leftDeriv_ne_rightDeriv hG).mono ?_
  intro t ht
  simp only [Set.mem_setOf_eq] at ht ⊢
  by_contra hdiff
  obtain ⟨A, hA, hne⟩ := ht
  obtain ⟨P, hP⟩ := fkgq_hcoup d N q hq t
  apply hne
  refine fk_unique_of_edgeMarg_eq hP ?_ hA
  intro e
  rw [fkgq_edgeMarg_free, fkgq_edgeMarg_wired]
  by_cases he : e ∈ (boxGraph d N).edgeFinset
  · obtain ⟨hf, hw⟩ :=
      fkgq_centered_deriv_eq_densities hd q hq hG hlim N e he t hdiff
    rw [hf, hw, hdiff]
  · rw [fkgq_free_density_nonEdge N e he (fsc_logistic_pos t)
      (fsc_logistic_lt_one t) hq,
      fkgq_wired_density_nonEdge N e he (fsc_logistic_pos t)
      (fsc_logistic_lt_one t) hq]

end StatMech.FK
