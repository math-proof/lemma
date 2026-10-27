import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Complex_exists_forall_ne_zero_re_gt_of_differentiableOn_of_exists_ne_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Complex_exists_forall_ne_zero_re_gt_of_differentiableOn_of_exists_ne_zero.lean)
-/
@[path]
private lemma main
  {ι : Type}
  {t : Finset ι}
  {f : ι → ℂ → ℂ}
  {σ σ' : ℝ}
  -- given
  (hf : ∀ i ∈ t, DifferentiableOn ℂ (f i) {s : ℂ | σ < s.re})
  (hne : ∀ i ∈ t, ∃ s : ℂ, σ < s.re ∧ f i s ≠ 0) :
  -- imply
  ∃ s : ℂ, σ' < s.re ∧ σ < s.re ∧ ∀ i ∈ t, f i s ≠ 0 := by
  -- proof
  classical
  set U : Set ℂ := {s : ℂ | σ < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt (r := σ)).isPreconnected
  have key : ∀ (t' : Finset ι), (∀ i ∈ t', DifferentiableOn ℂ (f i) U) → (∀ i ∈ t', ∃ s : ℂ, σ < s.re ∧ f i s ≠ 0) → ∀ V : Set ℂ, IsOpen V → V.Nonempty → V ⊆ U → ∃ s ∈ V, ∀ i ∈ t', f i s ≠ 0 := by
    intro t'
    refine Finset.induction_on t' ?_ ?_
    ·
      intro _ _ V _ hVne _
      obtain ⟨s, hs⟩ := hVne
      exact ⟨s, hs, fun i hi => (Finset.notMem_empty i hi).elim⟩
    ·
      intro a t' ha ih
      intro hdf hnz V hVo hVne hVU
      obtain ⟨s₀, hs₀V, hs₀⟩ := ih (fun i hi => hdf i (Finset.mem_insert_of_mem hi)) (fun i hi => hnz i (Finset.mem_insert_of_mem hi)) V hVo hVne hVU
      have hs₀U : s₀ ∈ U := hVU hs₀V
      have hev : ∀ᶠ z in nhds s₀, z ∈ V ∧ ∀ i ∈ t', f i z ≠ 0 := by
        refine (hVo.eventually_mem hs₀V).and ?_
        rw [Finset.eventually_all]
        intro i hi
        apply (((hdf i (Finset.mem_insert_of_mem hi)).differentiableAt (hUo.mem_nhds hs₀U)).continuousAt).eventually_ne (hs₀ i hi)
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hev
      have hfa : AnalyticOnNhd ℂ (f a) U := (hdf a (Finset.mem_insert_self a t')).analyticOnNhd hUo
      have hex : ∃ s ∈ Metric.ball s₀ ε, f a s ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have hzero : f a =ᶠ[nhds s₀] 0 := by
          filter_upwards [Metric.ball_mem_nhds s₀ hε] with z hz
          apply hcon z hz
        have hEq := hfa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hs₀U hzero
        obtain ⟨s₁, hs₁, hne₁⟩ := hnz a (Finset.mem_insert_self a t')
        apply hne₁ (hEq hs₁)
      obtain ⟨s, hsB, hfas⟩ := hex
      obtain ⟨hsV, hst⟩ := hball hsB
      refine ⟨s, hsV, ?_⟩
      intro i hi
      obtain rfl | hi' := Iff.mp Finset.mem_insert hi
      · apply hfas
      · apply hst i hi'
  set V : Set ℂ := {s : ℂ | max σ σ' < s.re} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hVne : V.Nonempty := by
    refine ⟨((max σ σ' + 1 : ℝ) : ℂ), ?_⟩
    show max σ σ' < ((max σ σ' + 1 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    linarith
  have hVU : V ⊆ U := by
    intro s hs
    change max σ σ' < s.re at hs
    change σ < s.re
    apply lt_of_le_of_lt (le_max_left _ _) hs
  obtain ⟨s, hsV, hs⟩ := key t (fun i hi => hf i hi) hne V hVo hVne hVU
  have hsV' : max σ σ' < s.re := hsV
  exact ⟨s, lt_of_le_of_lt (le_max_right _ _) hsV', lt_of_le_of_lt (le_max_left _ _) hsV', hs⟩


-- created on 2026-10-20
