/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.TwoDim.ZhangRotSymmetry.Part3
import Theorem.StatisticalMechanics.Code.Walls.binsclosure.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Def.StatisticalMechanics.Code.TwoDim.ZhangBKData.Part4
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Universality StatMech.Percolation StatMech.Walls


theorem zbd_twoScaleMerge_measurableSet {d : ℕ} (L R : Set (Site d)) (n : ℕ) :
    MeasurableSet (zbd_twoScaleMerge L R n) := by
  have heq : zbd_twoScaleMerge L R n = ⋃ x : Site d, ⋃ (_hx : x ∈ L),
      ⋃ y : Site d, ⋃ (_hy : y ∈ R),
        ({omega | (cluster d omega x).Infinite} ∩
          {omega | (cluster d omega y).Infinite}) ∩ zbd_connectedWithinBox x y n := by
    ext omega
    constructor
    · rintro ⟨x, hxL, y, hyR, hxinf, hyinf, hconn⟩
      exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hxL,
        Set.mem_iUnion.mpr ⟨y, Set.mem_iUnion.mpr ⟨hyR, ⟨⟨hxinf, hyinf⟩, hconn⟩⟩⟩⟩⟩
    · intro h
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp h
      obtain ⟨hxL, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hyR, hrest⟩ := Set.mem_iUnion.mp hy
      exact ⟨x, hxL, y, hyR, hrest.1.1, hrest.1.2, hrest.2⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro hx
  apply MeasurableSet.iUnion
  intro y
  apply MeasurableSet.iUnion
  intro hy
  exact ((measurableSet_clusterInfinite x).inter
    (measurableSet_clusterInfinite y)).inter (zbd_connectedWithinBox_measurableSet x y n)

theorem zbd_twoScaleError_measurableSet {d : ℕ} (L R : Set (Site d)) (n : ℕ) :
    MeasurableSet (zbd_twoScaleError L R n) :=
  ((zbd_sideHasInfinite_measurableSet L).inter
    (zbd_sideHasInfinite_measurableSet R)).diff
      (zbd_twoScaleMerge_measurableSet L R n)

theorem zbd_connectedWithinBox_mono {d : ℕ} (x y : Site d) :
    Monotone (zbd_connectedWithinBox x y) := by
  intro n m hnm omega
  rintro ⟨hx, hy, hxy⟩
  have hbox : box d n ⊆ box d m := by
    intro z hz
    rw [mem_box] at hz ⊢
    exact fun i => le_trans (hz i) hnm
  exact ⟨hbox hx, hbox hy,
    StatMech.RSW.Strip.connectedWithin_mono_set omega hbox hxy⟩

theorem zbd_twoScaleMerge_mono {d : ℕ} (L R : Set (Site d)) :
    Monotone (zbd_twoScaleMerge L R) := by
  intro n m hnm omega
  rintro ⟨x, hx, y, hy, hxinf, hyinf, hconn⟩
  exact ⟨x, hx, y, hy, hxinf, hyinf, zbd_connectedWithinBox_mono x y hnm hconn⟩

theorem zbd_twoScaleError_antitone {d : ℕ} (L R : Set (Site d)) :
    Antitone (zbd_twoScaleError L R) := by
  intro n m hnm omega herror
  exact ⟨herror.1, fun hm => herror.2 (zbd_twoScaleMerge_mono L R hnm hm)⟩


theorem zbd_iInter_twoScaleError_subset_atLeastTwo {d : ℕ} (L R : Set (Site d)) :
    (⋂ n, zbd_twoScaleError L R n) ⊆ atLeastTwoInfinite d := by
  intro omega herror
  have hcap := (Set.mem_iInter.mp herror 0).1
  obtain ⟨x, hxL, hxinf⟩ := hcap.1
  obtain ⟨y, hyR, hyinf⟩ := hcap.2
  have hnconn : ¬ Connected d omega x y := by
    intro hconn
    obtain ⟨n, hx, hy, hwithin⟩ := zbd_connectedWithin_box_of_connected omega hconn
    exact (Set.mem_iInter.mp herror n).2
      ⟨x, hxL, y, hyR, hxinf, hyinf, hx, hy, hwithin⟩
  have hcx : cluster d omega x ∈ infiniteClusters d omega := ⟨hxinf, x, rfl⟩
  have hcy : cluster d omega y ∈ infiniteClusters d omega := ⟨hyinf, y, rfl⟩
  have hcne : cluster d omega x ≠ cluster d omega y := by
    intro heq
    have : y ∈ cluster d omega x := heq ▸ self_mem_cluster omega y
    exact hnconn this
  have hnt : (infiniteClusters d omega).Nontrivial := ⟨_, hcx, _, hcy, hcne⟩
  have hone : (1 : ℕ∞) < (infiniteClusters d omega).encard :=
    Set.one_lt_encard_iff_nontrivial.mpr hnt
  show 2 ≤ numInfiniteClusters d omega
  rw [numInfiniteClusters, ← one_add_one_eq_two,
    ENat.add_one_le_iff ENat.one_ne_top]
  exact hone


theorem zbd_twoScaleError_tendsto_zero (L R : Set (Site 2)) :
    Tendsto (fun n => halfMeasure.real (zbd_twoScaleError L R n)) atTop (nhds 0) := by
  have hlim : Tendsto (fun n : ℕ => halfMeasure (zbd_twoScaleError L R n)) atTop
      (nhds (halfMeasure (⋂ n, zbd_twoScaleError L R n))) := tendsto_measure_iInter_atTop
    (μ := halfMeasure)
    (fun n => (zbd_twoScaleError_measurableSet L R n).nullMeasurableSet)
    (zbd_twoScaleError_antitone L R)
    ⟨0, measure_ne_top halfMeasure _⟩
  have hinter : halfMeasure (⋂ n, zbd_twoScaleError L R n) = 0 :=
    measure_mono_null (zbd_iInter_twoScaleError_subset_atLeastTwo L R)
      zbd_atLeastTwo_halfMeasure_zero
  rw [hinter] at hlim
  exact (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hlim


theorem zbd_exists_diagonal_outerRadius
    (L R : ℕ → Set (Site 2)) :
    ∃ M : ℕ → ℕ, (∀ n, n + 1 ≤ M n) ∧
      Tendsto (fun n => halfMeasure.real (zbd_twoScaleError (L n) (R n) (M n)))
        atTop (nhds 0) := by
  have hex : ∀ n : ℕ, ∃ m : ℕ, n + 1 ≤ m ∧
      halfMeasure.real (zbd_twoScaleError (L n) (R n) m) <
        1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hsmall : ∀ᶠ m : ℕ in atTop,
        halfMeasure.real (zbd_twoScaleError (L n) (R n) m) <
          1 / ((n : ℝ) + 1) :=
      (zbd_twoScaleError_tendsto_zero (L n) (R n)).eventually_lt_const hpos
    have hlarge : ∀ᶠ m : ℕ in atTop, n + 1 ≤ m := eventually_ge_atTop (n + 1)
    obtain ⟨m, hm, hmn⟩ := (hsmall.and hlarge).exists
    exact ⟨m, hmn, hm⟩
  choose M hMge hMsmall using hex
  refine ⟨M, hMge, ?_⟩
  have hupper : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => measureReal_nonneg) (fun n => (hMsmall n).le)


theorem zbd_twoScale_merge_cover {d : ℕ} (L R : Set (Site d)) (n : ℕ) :
    zbd_sideHasInfinite L ∩ zbd_sideHasInfinite R ⊆
      zbd_twoScaleMerge L R n ∪ zbd_twoScaleError L R n := by
  intro omega hcap
  by_cases hmerge : omega ∈ zbd_twoScaleMerge L R n
  · exact Or.inl hmerge
  · exact Or.inr ⟨hcap, hmerge⟩


theorem zbd_walk_first_hit_fn {omega : ConfigSpace (Sym2 (Site 2))} {x y : Site 2}
    (p : (openSubgraph 2 omega).Walk x y) (f : Site 2 → ℤ) (t : ℤ)
    (hstep : ∀ {u v}, (hypercubicLattice 2).Adj u v → (f u - f v).natAbs ≤ 1)
    (hx : f x < t) (hy : t ≤ f y) :
    ∃ j ≤ p.length, f (p.getVert j) = t ∧ ∀ m < j, f (p.getVert m) < t := by
  have hlen : t ≤ f (p.getVert p.length) := by rw [p.getVert_length]; exact hy
  classical
  let P : ℕ → Prop := fun m => t ≤ f (p.getVert m)
  have hPex : ∃ m, P m := ⟨p.length, hlen⟩
  let j := Nat.find hPex
  have hjP : t ≤ f (p.getVert j) := Nat.find_spec hPex
  have hjle : j ≤ p.length := Nat.find_le hlen
  have hbelow : ∀ m < j, f (p.getVert m) < t := by
    intro m hm
    have hnot := Nat.find_min hPex hm
    simpa [P, not_le] using hnot
  have hj0 : j ≠ 0 := by
    intro h0
    rw [h0, p.getVert_zero] at hjP
    exact (not_le_of_gt hx) hjP
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hkj : k < j := by omega
  have hkt : f (p.getVert k) < t := hbelow k hkj
  have hklt : k < p.length := by omega
  have hadj := p.adj_getVert_succ hklt
  rw [hk] at hjP
  have hdiff := hstep hadj.1
  have hle : f (p.getVert (k + 1)) ≤ t := by
    have habs : |f (p.getVert k) - f (p.getVert (k + 1))| ≤ 1 := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hdiff
    rw [abs_le] at habs
    omega
  refine ⟨k + 1, by omega, le_antisymm hle hjP, ?_⟩
  intro m hm
  exact hbelow m (by omega)


theorem zbd_connectedWithin_restrict_fn {omega : ConfigSpace (Sym2 (Site 2))}
    {S T : Set (Site 2)} {x y : Site 2} (hxS : x ∈ S) (hyS : y ∈ S)
    (h : ConnectedWithin 2 omega S ⟨x, hxS⟩ ⟨y, hyS⟩)
    (f : Site 2 → ℤ) (t : ℤ)
    (hstep : ∀ {u v}, (hypercubicLattice 2).Adj u v → (f u - f v).natAbs ≤ 1)
    (hx : f x < t) (hy : t ≤ f y)
    (hslab : ∀ z ∈ S, f z ≤ t → z ∈ T) :
    ∃ (u : Site 2) (_ : u ∈ S), f u = t ∧
      ∃ (huT : u ∈ T) (hxT : x ∈ T),
        ConnectedWithin 2 omega T ⟨x, hxT⟩ ⟨u, huT⟩ := by
  classical
  obtain ⟨w⟩ := h
  let p : (openSubgraph 2 omega).Walk x y :=
    w.map (SimpleGraph.Embedding.induce S).toHom
  have hpsupp : ∀ z ∈ p.support, z ∈ S := by
    intro z hz
    have hz' : z ∈ (w.map (SimpleGraph.Embedding.induce S).toHom).support := hz
    simp only [SimpleGraph.Walk.support_map, List.mem_map] at hz'
    obtain ⟨a, _ha, rfl⟩ := hz'
    exact a.2
  obtain ⟨j, hjle, hju, hjbelow⟩ :=
    zbd_walk_first_hit_fn p f t hstep hx hy
  let u : Site 2 := p.getVert j
  have huS : u ∈ S := hpsupp u (p.getVert_mem_support j)
  let q : (openSubgraph 2 omega).Walk x u := p.take j
  have hcoord : ∀ n ≤ j, f (p.getVert n) ≤ t := by
    intro n hn
    rcases lt_or_eq_of_le hn with hnj | rfl
    · exact le_of_lt (hjbelow n hnj)
    · exact le_of_eq hju
  have hqsupp : ∀ z ∈ q.support, z ∈ T := by
    intro z hz
    rw [SimpleGraph.Walk.take_support_eq_support_take_succ] at hz
    have hzp : z ∈ p.support := List.mem_of_mem_take hz
    have hzS : z ∈ S := hpsupp z hzp
    obtain ⟨m, hmlt, hmz⟩ := List.mem_iff_getElem.mp hz
    rw [List.length_take] at hmlt
    have hmle : m ≤ j := by omega
    have hzm : z = p.getVert m := by
      have hmp : m ≤ p.length := le_trans hmle hjle
      rw [List.getElem_take] at hmz
      rw [← hmz, ← SimpleGraph.Walk.getVert_eq_support_getElem p hmp]
    apply hslab z hzS
    rw [hzm]
    exact hcoord m hmle
  have hxT : x ∈ T := hqsupp x q.start_mem_support
  have huT : u ∈ T := hqsupp u q.end_mem_support
  exact ⟨u, huS, hju, huT, hxT, ⟨q.induce T hqsupp⟩⟩


end StatMech.TwoDim
