import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
open ContinuousRep
open scoped ComplexOrder


/--
[stronglyContinuous_of_continuousRep](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ContinuousRep.lean)
-/
@[path]
private lemma stronglyContinuous_of_continuousRep
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  {ρ : ContinuousRep G V} :
-- imply
  IsStronglyContinuous ρ.toMonoidHom := by
-- proof
  intro v
  exact ρ.continuous_action.comp (Continuous.prodMk continuous_id continuous_const)

/--
[continuousRep_of_stronglyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ContinuousRep.lean)
-/
@[path]
private lemma continuousRep_of_stronglyContinuous
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  [CompleteSpace V]
  [SequentialSpace (G × V)]
  {π : G →* (V →L[ℂ] V)}
-- given
  (hsc : IsStronglyContinuous π) :
-- imply
  Continuous (fun p : G × V => (π p.1) p.2) := by
-- proof
  apply SeqContinuous.continuous
  intro u p hu
  have hg : Filter.Tendsto (fun n => (u n).1) Filter.atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hu
  have hv : Filter.Tendsto (fun n => (u n).2) Filter.atTop (nhds p.2) :=
    (continuous_snd.tendsto p).comp hu
  have hconv : Filter.Tendsto (fun n => (π (u n).1) p.2) Filter.atTop
    (nhds ((π p.1) p.2)) :=
    ((hsc p.2).tendsto p.1).comp hg
  have hptwise : ∀ w : V, ∃ C, ∀ n, ‖(π (u n).1) w‖ ≤ C := by
    intro w
    have hw := ((hsc w).tendsto p.1).comp hg
    have hb := hw.norm.isBoundedUnder_le.bddAbove_range
    rw [bddAbove_def] at hb; obtain ⟨C, hC⟩ := hb
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hptwise
  have hdiff : Filter.Tendsto (fun n => (u n).2 - p.2) Filter.atTop (nhds 0) := by
    rw [← sub_self p.2]; exact hv.sub tendsto_const_nhds
  have herr : Filter.Tendsto (fun n => (π (u n).1) ((u n).2 - p.2))
    Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop] at hdiff ⊢
    intro ε hε
    if hC0 : C ≤ 0 then
      obtain ⟨N, hN⟩ := hdiff ε hε
      exact ⟨N, fun n hn => by
        simp only [dist_zero_right]
        calc
          _ ≤ ‖π (u n).1‖ * ‖(u n).2 - p.2‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ 0 * ‖(u n).2 - p.2‖ :=
            mul_le_mul_of_nonneg_right ((hC n).trans hC0) (norm_nonneg _)
          _ = 0 := zero_mul _
          _ < ε := hε⟩
    else
      push Not at hC0
      obtain ⟨N, hN⟩ := hdiff (ε / C) (div_pos hε hC0)
      exact ⟨N, fun n hn => by
        simp only [dist_zero_right] at hN ⊢
        calc
          _ ≤ ‖π (u n).1‖ * ‖(u n).2 - p.2‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ C * ‖(u n).2 - p.2‖ :=
            mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _)
          _ < C * (ε / C) := by
            apply mul_lt_mul_of_pos_left (hN n hn) hC0
          _ = ε := mul_div_cancel₀ ε (ne_of_gt hC0)⟩
  show Filter.Tendsto ((fun p => (π p.1) p.2) ∘ u) Filter.atTop (nhds ((π p.1) p.2))
  have : Filter.Tendsto (fun n => (π (u n).1) ((u n).2 - p.2) + (π (u n).1) p.2)
    Filter.atTop (nhds ((π p.1) p.2)) := by
    rw [show (π p.1) p.2 = 0 + (π p.1) p.2 from (zero_add _).symm]
    exact herr.add hconv
  apply Filter.Tendsto.congr (fun n => _) this
  simp [Function.comp, map_sub, sub_add_cancel]

/--
[continuousRep_iff_stronglyContinuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ContinuousRep.lean)
-/
@[path]
private lemma continuousRep_iff_stronglyContinuous
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup V]
  [NormedSpace ℂ V]
  [CompleteSpace V]
  [SequentialSpace (G × V)]
  {π : G →* (V →L[ℂ] V)} :
-- imply
  Continuous (fun p : G × V => (π p.1) p.2) ↔ IsStronglyContinuous π :=
-- proof
  ⟨fun hcont => stronglyContinuous_of_continuousRep (ρ := ⟨π, hcont⟩),
    fun hsc => continuousRep_of_stronglyContinuous hsc⟩


-- created on 2026-10-23
-- updated on 2026-10-26
