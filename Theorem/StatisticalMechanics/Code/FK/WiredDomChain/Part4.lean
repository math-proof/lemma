/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredDomChain.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.InducedBC.Part11
import Theorem.StatisticalMechanics.Code.FK.WiredBoxLimit.Part2
import Theorem.StatisticalMechanics.Code.FK.BoxTailLimit
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.FK.TailLimit.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay.Part2
import Def.StatisticalMechanics.Code.FK.WiredDomChain.Part4
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}


theorem isIncreasing_connToBdryEventLE (d : ℕ) {n m : ℕ} (h : n ≤ m) :
    IsIncreasing (connToBdryEventLE d h) := by
  intro a b hab ha
  simp only [connToBdryEventLE, Set.mem_preimage, Set.mem_setOf_eq] at ha ⊢
  obtain ⟨y, hy, hconn⟩ := ha
  exact ⟨y, hy, hconn.mono (openSub_mono _ (boxRestrictLE_monotone d h hab))⟩


theorem boxBdryConnEvent_eq_boxRestrict_preimage (d : ℕ) {n m : ℕ} (h : n ≤ m) :
    boxBdryConnEvent d n = boxRestrict d m ⁻¹' (connToBdryEventLE d h) := by
  ext ω
  simp only [boxBdryConnEvent, connToBdryEventLE, Set.mem_preimage, Set.mem_setOf_eq,
    boxRestrictLE_boxRestrict]

theorem measurableSet_boxRestrict_connToBdryEventLE (d : ℕ) {n m : ℕ} (h : n ≤ m) :
    MeasurableSet (boxRestrict d m ⁻¹' (connToBdryEventLE d h)) := by
  rw [← boxBdryConnEvent_eq_boxRestrict_preimage d h]
  exact measurableSet_boxBdryConnEvent d n


theorem wiredFiniteMeasure_real_boxRestrictEvent (m : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (S : Set (ConfigSpace (Sym2 (boxVerts d m))))
    (hmeas : MeasurableSet (boxRestrict d m ⁻¹' S)) :
    (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d m ⁻¹' S)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d m)),
          S.indicator (fun _ => (1:ℝ)) ω * wiredFkProb (boxGraph d m) (boxBoundary d m) p 2 ω := by
  have hw : (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure _).real
        (boxRestrict d m ⁻¹' S)
      = ((wiredFkPMF (boxGraph d m) (boxBoundary d m) hp hp1
            (by norm_num : (0:ℝ) < 2)).toMeasure
          (extendEdge d m ⁻¹' (boxRestrict d m ⁻¹' S))).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d m) hmeas]
  have hpre : extendEdge d m ⁻¹' (boxRestrict d m ⁻¹' S) = S := by
    ext ω
    simp only [Set.mem_preimage, boxRestrict_extendEdge]
  rw [hw, hpre, wiredFkPMF_toMeasure_toReal d m hp hp1 (by norm_num : (0:ℝ) < 2)]


theorem wiredFiniteMeasure_succ_le_boxBdryConnEvent_le (n m : ℕ) (h : n ≤ m) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d (m+1) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
      ≤ (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
  have hmeas := measurableSet_boxRestrict_connToBdryEventLE d h
  have hstep := wiredFiniteMeasure_succ_le_smallerBox m hp hp1
    (isIncreasing_connToBdryEventLE d h) hmeas
  rw [boxBdryConnEvent_eq_boxRestrict_preimage d h (n := n),
    wiredFiniteMeasure_real_boxRestrictEvent m hp hp1 (connToBdryEventLE d h) hmeas]
  exact hstep


theorem wiredFiniteMeasure_boxBdryConnEvent_antitone_radius (n k : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d (n+k+1) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
      ≤ (wiredFiniteMeasure d (n+k) hp hp1 (by norm_num : (0:ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) :=
  wiredFiniteMeasure_succ_le_boxBdryConnEvent_le n (n+k) (Nat.le_add_right n k) hp hp1


theorem openSubgraph_adj_of_boxGraph (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {x y : boxVerts d n} (h : (openSub (boxGraph d n) (boxRestrict d n ω)).Adj x y) :
    (openSubgraph d ω).Adj (x : Site d) (y : Site d) := by
  rw [openSub_adj] at h
  obtain ⟨hadj, hopen⟩ := h
  rw [boxGraph, SimpleGraph.comap_adj] at hadj
  refine ⟨hadj, ?_⟩
  have hev : boxRestrict d n ω s(x, y) = ω s((x:Site d), (y:Site d)) := by
    show ω (edgeIncl d n s(x,y)) = ω s((x:Site d),(y:Site d))
    unfold edgeIncl
    rw [Sym2.map_mk]
  rw [hev] at hopen
  exact hopen


theorem connected_of_boxConnected (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {x y : boxVerts d n}
    (h : (openSub (boxGraph d n) (boxRestrict d n ω)).Reachable x y) :
    StatMech.Lattice.Connected d ω (x : Site d) (y : Site d) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  unfold StatMech.Lattice.Connected
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail u w _ hadj ih => exact ih.tail (openSubgraph_adj_of_boxGraph n ω hadj)


theorem boxBdryConnEvent_subset_crossingEvent (n : ℕ) :
    boxBdryConnEvent d n ⊆ crossingEvent d n := by
  intro ω hω
  simp only [boxBdryConnEvent, Set.mem_preimage, Set.mem_setOf_eq, ConnToBdry] at hω
  obtain ⟨v, hv, hconn⟩ := hω
  rw [mem_crossingEvent]
  refine ⟨(v : Site d), connected_of_boxConnected n ω hconn, ?_⟩
  rw [boxBoundary, mem_vertexBoundary] at hv
  exact hv.2


theorem boxGraph_open_of_openSubgraph (n : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    {x y : boxVerts d n} (h : (openSubgraph d ω).Adj (x : Site d) (y : Site d)) :
    (openSub (boxGraph d n) (boxRestrict d n ω)).Adj x y := by
  rw [openSubgraph_adj] at h
  obtain ⟨hadj, hopen⟩ := h
  rw [openSub_adj]
  refine ⟨by rw [boxGraph, SimpleGraph.comap_adj]; exact hadj, ?_⟩
  show ω (edgeIncl d n s(x,y)) = true
  unfold edgeIncl
  rw [Sym2.map_mk]
  exact hopen


theorem boxBdryConn_of_crossing (n : ℕ) (hn : 1 ≤ n) (ω : ConfigSpace (Sym2 (Site d)))
    {v : Site d} (hv : v ∉ box d n)
    (h : (openSubgraph d ω).Reachable (origin d) v) :
    ConnToBdry (boxGraph d n) (boxBoundary d n) (boxRestrict d n ω) (IsingFK.boxOrigin d n) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  set OS := openSubgraph d ω
  set os := openSub (boxGraph d n) (boxRestrict d n ω)
  suffices H : ∀ w : Site d, Relation.ReflTransGen OS.Adj (origin d) w →
      (ConnToBdry (boxGraph d n) (boxBoundary d n) (boxRestrict d n ω) (IsingFK.boxOrigin d n)
        ∨ ∃ x : boxVerts d n, (x : Site d) = w ∧ os.Reachable (IsingFK.boxOrigin d n) x) by
    rcases H v h with hdone | ⟨x, hx, _⟩
    · exact hdone
    · exact absurd (hx ▸ x.2) hv
  intro w hw
  induction hw with
  | refl => exact Or.inr ⟨IsingFK.boxOrigin d n, rfl, SimpleGraph.Reachable.refl _⟩
  | @tail u w hru hadj ih =>
      rcases ih with hdone | ⟨x, hx, hreach⟩
      · exact Or.inl hdone
      · subst hx
        by_cases hw_box : w ∈ box d n
        · refine Or.inr ⟨⟨w, hw_box⟩, rfl,
            hreach.trans (boxGraph_open_of_openSubgraph n ω hadj).reachable⟩
        · left
          rw [openSubgraph_adj] at hadj
          obtain ⟨hnn, _⟩ := hadj
          rw [hypercubicLattice_adj] at hnn
          have hnn' : StatMech.Lattice.NearestNeighbour d (x : Site d) w := hnn
          exact ⟨x, ⟨x.2, notMem_box_pred_of_adj_outer hn x.2 hnn' hw_box⟩, hreach⟩


theorem crossingEvent_succ_subset_boxBdryConnEvent (n : ℕ) (hn : 1 ≤ n) :
    crossingEvent d (n+1) ⊆ boxBdryConnEvent d n := by
  intro ω hω
  rw [mem_crossingEvent] at hω
  obtain ⟨v, hconn, hv⟩ := hω
  simp only [Nat.add_sub_cancel] at hv
  simp only [boxBdryConnEvent, Set.mem_preimage, Set.mem_setOf_eq]
  exact boxBdryConn_of_crossing n hn ω hv hconn


theorem wiredIv_boxBdryConnEvent_tendsto {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    Tendsto (fun n => ((wiredInfiniteVolume d hp hp1 hq :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
        Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n))
      atTop (𝓝 (fkTheta d hp hp1 hq (q := q))) := by
  set μ : Measure (ConfigSpace (Sym2 (Site d))) :=
    ((wiredInfiniteVolume d hp hp1 hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))) with hμ
  have htail : Tendsto (fun n => μ.real (crossingEvent d n)) atTop
      (𝓝 (fkTheta d hp hp1 hq (q := q))) :=
    fkBoundaryConnReal_tendsto_fkTheta hp hp1 hq
  have htail_shift : Tendsto (fun n => μ.real (crossingEvent d (n+1))) atTop
      (𝓝 (fkTheta d hp hp1 hq (q := q))) := htail.comp (tendsto_add_atTop_nat 1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' htail_shift htail ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact measureReal_mono (crossingEvent_succ_subset_boxBdryConnEvent n hn)
  · filter_upwards with n
    exact measureReal_mono (boxBdryConnEvent_subset_crossingEvent n)


theorem boxBdryConnEvent_subset_le (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    boxBdryConnEvent d n ⊆ boxBdryConnEvent d k := by
  induction n with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_or_ge k (m+1) with hlt | _
      · exact (boxBdryConnEvent_succ_subset m (by omega)).trans (ih (by omega))
      · rw [show k = m+1 by omega]


theorem radius_antitone (k : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Antitone (fun j => (wiredFiniteMeasure d (k+j) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k)) := by
  apply antitone_nat_of_succ_le
  intro j
  have := wiredFiniteMeasure_succ_le_boxBdryConnEvent_le (d := d) k (k+j)
    (Nat.le_add_right k j) hp hp1
  simpa [Nat.add_assoc] using this


theorem tendsto_of_antitone_of_subseq {a : ℕ → ℝ} {L : ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hanti : Antitone a) (hbdd : BddBelow (Set.range a))
    (hsub : Tendsto (fun m => a (φ m)) atTop (𝓝 L)) :
    Tendsto a atTop (𝓝 L) := by
  have hinf : Tendsto a atTop (𝓝 (⨅ n, a n)) := tendsto_atTop_ciInf hanti hbdd
  rw [tendsto_nhds_unique hsub (hinf.comp hφ.tendsto_atTop)]
  exact hinf


theorem wiredFiniteMeasure_radius_tendsto (k : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun j => (wiredFiniteMeasure d (k+j) hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k))
      atTop (𝓝 (((wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) :
          ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
          Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k))) := by
  classical
  have hq : (0:ℝ) < 2 := by norm_num
  set a' := fun j => (wiredFiniteMeasure d (k+j) hp hp1 hq
      : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k) with ha'
  set bk := ((wiredInfiniteVolume d hp hp1 hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k) with hbk
  obtain ⟨φ, hφ, hconv⟩ := wiredInfiniteVolume_isLimit d hp hp1 hq
  have hport : Tendsto (fun m => (wiredFiniteMeasure d (φ m) hp hp1 hq
      : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k))
      atTop (𝓝 bk) := hconv.tendsto_real_of_isClopen (isClopen_boxBdryConnEvent d k)
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  obtain ⟨m₀, hm₀⟩ := (hφtop.eventually_ge_atTop k).exists_forall_of_atTop
  refine tendsto_of_antitone_of_subseq (φ := fun m => φ (m + m₀) - k) ?_
    (radius_antitone k hp hp1) ⟨0, by rintro x ⟨j, rfl⟩; exact measureReal_nonneg⟩ ?_
  · intro i j hij
    simp only
    have hi : k ≤ φ (i + m₀) := hm₀ (i + m₀) (by omega)
    have hj : k ≤ φ (j + m₀) := hm₀ (j + m₀) (by omega)
    have hlt : φ (i + m₀) < φ (j + m₀) := hφ (by omega)
    omega
  · have hsub : Tendsto (fun m => (wiredFiniteMeasure d (φ (m+m₀)) hp hp1 hq
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d k))
        atTop (𝓝 bk) := hport.comp (tendsto_add_atTop_nat m₀)
    refine hsub.congr (fun m => ?_)
    have hge : k ≤ φ (m + m₀) := hm₀ (m + m₀) (by omega)
    simp only [ha']
    have : k + (φ (m + m₀) - k) = φ (m + m₀) := by omega
    rw [this]


theorem boxBdryConnEvent_diag_tendsto {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n => (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n))
      atTop (𝓝 (fkTheta d hp hp1 (by norm_num : (0:ℝ) < 2) (q := 2))) := by
  classical
  have hq : (0:ℝ) < 2 := by norm_num
  set μ := fun m => (wiredFiniteMeasure d m hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))) with hμ
  set ν := ((wiredInfiniteVolume d hp hp1 hq : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))) :
      Measure (ConfigSpace (Sym2 (Site d)))) with hν
  set aN := fun n => (μ n).real (boxBdryConnEvent d n) with haN
  set bN := fun k => ν.real (boxBdryConnEvent d k) with hbN
  set fk := fkTheta d hp hp1 hq (q := 2) with hfk
  have haprime : ∀ k, Tendsto (fun j => (μ (k+j)).real (boxBdryConnEvent d k)) atTop (𝓝 (bN k)) :=
    fun k => wiredFiniteMeasure_radius_tendsto k hp hp1
  
  set a1 := fun j => aN (j+1) with ha1
  have ha1_anti : Antitone a1 := by
    apply antitone_nat_of_succ_le
    intro j
    exact wiredFiniteMeasure_boxBdryConnEvent_antitone (j+1) (by omega) hp hp1
  have ha1_bdd : BddBelow (Set.range a1) := ⟨0, by rintro x ⟨j, rfl⟩; exact measureReal_nonneg⟩
  have haN_tendsto : Tendsto aN atTop (𝓝 (⨅ j, a1 j)) :=
    (tendsto_add_atTop_iff_nat (f := aN) 1).mp (tendsto_atTop_ciInf ha1_anti ha1_bdd)
  set L := ⨅ j, a1 j with hL
  suffices hLfk : L = fk by rw [hLfk] at haN_tendsto; exact haN_tendsto
  have hbN_tendsto : Tendsto bN atTop (𝓝 fk) := wiredIv_boxBdryConnEvent_tendsto hp hp1 hq
  apply le_antisymm
  · 
    have hLle : ∀ k, 1 ≤ k → L ≤ bN k := by
      intro k hk
      have hbound : ∀ j, aN (k+j) ≤ (μ (k+j)).real (boxBdryConnEvent d k) := fun j =>
        measureReal_mono (boxBdryConnEvent_subset_le k (k+j) hk (Nat.le_add_right k j))
      have hktop : Tendsto (fun j => k + j) atTop atTop :=
        tendsto_atTop_mono (fun j => Nat.le_add_left j k) tendsto_id
      have hL1 : Tendsto (fun j => aN (k+j)) atTop (𝓝 L) := haN_tendsto.comp hktop
      exact le_of_tendsto_of_tendsto' hL1 (haprime k) hbound
    refine ge_of_tendsto hbN_tendsto ?_
    filter_upwards [eventually_ge_atTop 1] with k hk using hLle k hk
  · 
    have hbk_le : ∀ k, bN k ≤ aN k := by
      intro k
      have hanti_k := radius_antitone (d := d) k hp hp1
      have hle : bN k ≤ (μ (k+0)).real (boxBdryConnEvent d k) := by
        refine le_of_tendsto (haprime k) ?_
        filter_upwards [eventually_ge_atTop 0] with j _ using hanti_k (Nat.zero_le j)
      have hk0 : aN k = (μ (k+0)).real (boxBdryConnEvent d k) := by simp [haN]
      rw [hk0]; exact hle
    exact le_of_tendsto_of_tendsto' hbN_tendsto haN_tendsto hbk_le


theorem boxBoundaryConnProfile_tendsto {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n => IsingFK.boxBoundaryConnProfile d hp hp1 (by norm_num : (0:ℝ) < 2) n)
      atTop (𝓝 (fkTheta d hp hp1 (by norm_num : (0:ℝ) < 2) (q := 2))) :=
  boxBoundaryConnProfile_tendsto_of_diag d hp hp1 (boxBdryConnEvent_diag_tendsto hp hp1)

end FK
end StatMech
