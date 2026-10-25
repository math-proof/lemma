/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/Atomless.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.MonotoneConvergence
import Def.MeasureTheory.Measure.Atomless.Part3


section

open MeasureTheory Set Filter Topology

namespace MeasureTheory

/-- Measures add along the Sierpinski iteration. -/
theorem sierpinskiSeq_measure_add {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {s : Set α}
    {t : ENNReal} (ht : t ≤ μ s) (n : ℕ) :
    μ ((sierpinskiSeq ht (n + 1)).u) = μ ((sierpinskiSeq ht n).u) +
      μ (sierpinskiPiece ht (sierpinskiSeq ht n)) := by
  have hspec := sierpinskiPiece_spec ht (sierpinskiSeq ht n)
  have hdisj : Disjoint ((sierpinskiSeq ht n).u)
      (sierpinskiPiece ht (sierpinskiSeq ht n)) :=
    (Set.disjoint_left.mpr (fun x hx => (hspec.2.1 hx).2)).symm
  rw [sierpinskiSeq_succ ht n, measure_union hdisj hspec.1]

/-- In a finite atomless measure, every measurable set contains measurable subsets of
every smaller measure. -/
theorem isAtomless_exists_subset_measure_eq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (hA : IsAtomless μ)
    {s : Set α} (hs : MeasurableSet s) {t : ENNReal} (ht : t ≤ μ s) :
    ∃ u, u ⊆ s ∧ MeasurableSet u ∧ μ u = t := by
  have hmono : Monotone (fun n => ((sierpinskiSeq ht n).u)) :=
    sierpinskiSeq_mono ht
  have hmono_a : Monotone (fun n => μ.real ((sierpinskiSeq ht n).u)) := by
    intro m n hmn
    exact ENNReal.toReal_mono ((measure_lt_top μ _).ne)
      (measure_mono (hmono hmn))
  have ht_ne : t ≠ ⊤ := ne_top_of_le_ne_top (measure_lt_top μ s).ne ht
  have hbdd : BddAbove
      (Set.range (fun n => μ.real ((sierpinskiSeq ht n).u))) := by
    refine ⟨t.toReal, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact ENNReal.toReal_mono ht_ne (sierpinskiSeq ht n).hle
  obtain ⟨A, hA_lim⟩ :
      ∃ A, Tendsto (fun n => μ.real ((sierpinskiSeq ht n).u)) atTop (𝓝 A) :=
    ⟨_, tendsto_atTop_ciSup hmono_a hbdd⟩
  have hshift : Tendsto (fun n => μ.real ((sierpinskiSeq ht (n + 1)).u)) atTop
      (𝓝 A) :=
    (Filter.tendsto_add_atTop_iff_nat 1).mpr hA_lim
  have hdiff_lim : Tendsto
      (fun n => μ.real ((sierpinskiSeq ht (n + 1)).u) -
        μ.real ((sierpinskiSeq ht n).u)) atTop (𝓝 0) := by
    have h := hshift.sub hA_lim
    rwa [sub_self] at h
  have hpiece_eq : ∀ n, μ.real (sierpinskiPiece ht (sierpinskiSeq ht n))
      = μ.real ((sierpinskiSeq ht (n + 1)).u) -
        μ.real ((sierpinskiSeq ht n).u) := by
    intro n
    have hfin2 : μ ((sierpinskiSeq ht n).u) ≠ ⊤ :=
      (measure_lt_top μ _).ne
    have hfin3 : μ (sierpinskiPiece ht (sierpinskiSeq ht n)) ≠ ⊤ :=
      (measure_lt_top μ _).ne
    simp only [measureReal_def, sierpinskiSeq_measure_add ht n,
      ENNReal.toReal_add hfin2 hfin3]
    ring
  have hpiece_lim : Tendsto
      (fun n => μ.real (sierpinskiPiece ht (sierpinskiSeq ht n))) atTop
      (𝓝 0) :=
    hdiff_lim.congr (fun n => (hpiece_eq n).symm)
  have hcap_le2 : ∀ n, (sierpinskiCap μ s t ((sierpinskiSeq ht n).u)).toReal
      ≤ 2 * μ.real (sierpinskiPiece ht (sierpinskiSeq ht n)) := by
    intro n
    have hspec := sierpinskiPiece_spec ht (sierpinskiSeq ht n)
    have hfin : μ (sierpinskiPiece ht (sierpinskiSeq ht n)) ≠ ⊤ :=
      (measure_lt_top μ _).ne
    have hcap_le : sierpinskiCap μ s t ((sierpinskiSeq ht n).u)
        ≤ μ (sierpinskiPiece ht (sierpinskiSeq ht n)) +
          μ (sierpinskiPiece ht (sierpinskiSeq ht n)) := by
      have hadd := ENNReal.add_halves
        (sierpinskiCap μ s t ((sierpinskiSeq ht n).u))
      rw [← hadd]
      exact add_le_add hspec.2.2.2 hspec.2.2.2
    have hsum_ne : μ (sierpinskiPiece ht (sierpinskiSeq ht n)) +
        μ (sierpinskiPiece ht (sierpinskiSeq ht n)) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hfin, hfin⟩
    have hto := ENNReal.toReal_mono hsum_ne hcap_le
    rw [ENNReal.toReal_add hfin hfin] at hto
    rw [measureReal_def]
    linarith
  have hcap_lim : Tendsto
      (fun n => (sierpinskiCap μ s t ((sierpinskiSeq ht n).u)).toReal)
      atTop (𝓝 0) := by
    have h2lim : Tendsto
        (fun n => 2 * μ.real (sierpinskiPiece ht (sierpinskiSeq ht n)))
        atTop (𝓝 0) := by
      have h := Filter.Tendsto.const_mul 2 hpiece_lim
      simpa using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      h2lim ?_ ?_
    · exact Eventually.of_forall (fun n => ENNReal.toReal_nonneg)
    · exact Eventually.of_forall hcap_le2
  have hwmeas : MeasurableSet (⋃ n, ((sierpinskiSeq ht n).u)) :=
    MeasurableSet.iUnion (fun n => (sierpinskiSeq ht n).hmeas)
  have hwsub : (⋃ n, ((sierpinskiSeq ht n).u)) ⊆ s :=
    Set.iUnion_subset (fun n => (sierpinskiSeq ht n).hsub)
  have hμw : μ (⋃ n, ((sierpinskiSeq ht n).u)) ≤ t := by
    rw [hmono.measure_iUnion]
    exact iSup_le (fun n => (sierpinskiSeq ht n).hle)
  by_cases hlt : μ (⋃ n, ((sierpinskiSeq ht n).u)) < t
  · have hgap_ne : t - μ (⋃ n, ((sierpinskiSeq ht n).u)) ≠ 0 := by
      intro h0
      have h1 := tsub_add_cancel_of_le hμw
      rw [h0, zero_add] at h1
      exact (ne_of_lt hlt) h1
    have hgap_pos : 0 < t - μ (⋃ n, ((sierpinskiSeq ht n).u)) :=
      bot_lt_iff_ne_bot.mpr hgap_ne
    have hgap_ne_top : t - μ (⋃ n, ((sierpinskiSeq ht n).u)) ≠ ⊤ :=
      ne_top_of_le_ne_top ht_ne tsub_le_self
    have hgap_real : 0
        < (t - μ (⋃ n, ((sierpinskiSeq ht n).u))).toReal :=
      ENNReal.toReal_pos_iff.mpr
        ⟨hgap_pos, lt_top_iff_ne_top.mpr hgap_ne_top⟩
    have hinter : μ (s ∩ (⋃ n, ((sierpinskiSeq ht n).u))) +
        μ (s \ (⋃ n, ((sierpinskiSeq ht n).u))) = μ s :=
      measure_inter_add_sdiff s hwmeas
    have hsdiff : s ∩ (⋃ n, ((sierpinskiSeq ht n).u)) =
        ⋃ n, ((sierpinskiSeq ht n).u) :=
      Set.inter_eq_self_of_subset_right hwsub
    rw [hsdiff] at hinter
    have hrem_ne : μ (s \ (⋃ n, ((sierpinskiSeq ht n).u))) ≠ 0 := by
      intro h0
      rw [h0, add_zero] at hinter
      have hltμ : μ (⋃ n, ((sierpinskiSeq ht n).u)) < μ s :=
        lt_of_lt_of_le hlt ht
      exact (ne_of_lt hltμ) hinter
    have hrem_pos : 0 < μ (s \ (⋃ n, ((sierpinskiSeq ht n).u))) :=
      bot_lt_iff_ne_bot.mpr hrem_ne
    have hrem_meas : MeasurableSet (s \ (⋃ n, ((sierpinskiSeq ht n).u))) :=
      hs.diff hwmeas
    obtain ⟨w, hwsub', hwmeas, hwpos, hwle⟩ :=
      isAtomless_exists_small_subset_le hA hrem_meas hrem_pos hgap_real
    rw [measureReal_def] at hwle
    have hwfin : μ w ≠ ⊤ := (measure_lt_top μ w).ne
    have hw_le_gap : μ w ≤ t - μ (⋃ n, ((sierpinskiSeq ht n).u)) :=
      (ENNReal.toReal_le_toReal hwfin hgap_ne_top).mp hwle
    have hadm : ∀ n, μ w ≤
        sierpinskiCap μ s t ((sierpinskiSeq ht n).u) := by
      intro n
      apply le_sSup
      refine ⟨w, hwmeas, ?_, ?_, rfl⟩
      · intro x hx
        have hx2 := hwsub' hx
        refine ⟨hx2.1, ?_⟩
        intro hxmem
        exact hx2.2 (Set.mem_iUnion_of_mem n hxmem)
      · have h1 : μ ((sierpinskiSeq ht n).u) ≤
            μ (⋃ n, ((sierpinskiSeq ht n).u)) :=
          measure_mono
            (Set.subset_iUnion (fun k => ((sierpinskiSeq ht k).u)) n)
        have h2 : μ (⋃ n, ((sierpinskiSeq ht n).u)) + μ w ≤ t :=
          add_le_of_le_tsub_left_of_le hμw hw_le_gap
        calc μ ((sierpinskiSeq ht n).u) + μ w
            ≤ μ (⋃ n, ((sierpinskiSeq ht n).u)) + μ w :=
              add_le_add_left h1 _
          _ ≤ t := h2
    have hw_real_pos : 0 < μ.real w := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos_iff.mpr
        ⟨hwpos, lt_top_iff_ne_top.mpr hwfin⟩
    have hle_all : ∀ n, μ.real w ≤
        (sierpinskiCap μ s t ((sierpinskiSeq ht n).u)).toReal := by
      intro n
      rw [measureReal_def]
      exact ENNReal.toReal_mono
        (ne_top_of_le_ne_top ht_ne sierpinskiCap_le) (hadm n)
    obtain ⟨n, hn⟩ := (hcap_lim.eventually_lt_const hw_real_pos).exists
    exact (lt_irrefl _ (lt_of_le_of_lt (hle_all n) hn)).elim
  · have heq : μ (⋃ n, ((sierpinskiSeq ht n).u)) = t :=
      le_antisymm hμw (not_lt.mp hlt)
    exact ⟨⋃ n, ((sierpinskiSeq ht n).u), hwsub, hwmeas, heq⟩

end MeasureTheory
end
