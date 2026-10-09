import Mathlib
import sympy.series.limits
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {b δ : ℝ}
-- given
  (hcont : ContinuousOn f (Set.Iio b))
  (hδ : δ > 0)
  (h : ∀ ε ∈ Set.Ioc 0 δ, ∃ L > 0, lim [x → b - ε] f x = L) :
-- imply
  ∀ L, (lim [x → b⁻] f x = L) → 0 ≤ L := by
-- proof
  have hpos : ∀ x ∈ Set.Ico (b - δ) b, 0 < f x := by
    intro x hx
    obtain ⟨hxb, hlt⟩ := Set.mem_Ico.mp hx
    obtain ⟨L, hL, hlim⟩ := h (b - x) ⟨by linarith, by linarith⟩
    rw [sub_sub_cancel] at hlim
    have hcx : ContinuousAt f x :=
      hcont.continuousAt (IsOpen.mem_nhds isOpen_Iio (Set.mem_Iio.2 hlt))
    have hlim' : Filter.Tendsto (fun x ↦ f x) (nhdsWithin x {x}ᶜ) (nhds (f x)) :=
      hcx.tendsto.mono_left nhdsWithin_le_nhds
    rwa [← (tendsto_nhds_unique_inseparable hlim hlim').eq]
  intro L hL
  apply le_of_not_gt
  intro hL0
  have hnbhd : Set.Iio (L / 2) ∈ nhds L :=
    IsOpen.mem_nhds isOpen_Iio (Set.mem_Iio.2 (by linarith))
  have hneg : ∀ᶠ x in nhdsWithin b (Set.Iio b), f x < L / 2 :=
    Filter.tendsto_def.1 hL _ hnbhd
  have hpos_ev : ∀ᶠ x in nhdsWithin b (Set.Iio b), 0 ≤ f x := by
    apply Filter.eventually_iff_exists_mem.2
      ⟨Set.Ico (b - δ) b, _, fun x hx => (hpos x hx).le⟩
    apply mem_nhdsWithin.2
      ⟨Set.Ioi (b - δ), isOpen_Ioi, Set.mem_Ioi.2 (by linarith),
        fun x hx => Set.mem_Ico.mpr ⟨hx.1.le, hx.2⟩⟩
  obtain ⟨t, ht, hsub⟩ := Filter.eventually_iff_exists_mem.1 (hneg.and hpos_ev)
  obtain ⟨x, hx⟩ := Filter.nonempty_of_mem ht
  obtain ⟨h1, h2⟩ := hsub x hx
  linarith


-- created on 2026-10-07
