import Mathlib
import sympy.Basic
open scoped Manifold ContDiff Topology
open Filter Set


private lemma nhdsNE_neBot {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] (z : M) : (𝓝[≠] z).NeBot := by
  set e := extChartAt 𝓘(ℂ, ℂ) z with he
  have hc : ContinuousAt e.symm (e z) := continuousAt_extChartAt_symm z
  have htgt : e.target ∈ 𝓝 (e z) := extChartAt_target_mem_nhds z
  apply Tendsto.neBot
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    ·
      have h1 : Tendsto e.symm (𝓝 (e z)) (𝓝 (e.symm (e z))) := hc.tendsto
      rw [extChartAt_to_inv] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    ·
      refine eventually_nhdsWithin_iff.2 ?_
      filter_upwards [htgt] with y hyt hne
      intro heq
      apply hne
      calc
        _ = e (e.symm y) := (e.right_inv hyt).symm
        _ = e z := by rw [show e.symm y = z from heq]

private lemma isOpen_setOf_eventually_nhdsNE {M : Type*} [TopologicalSpace M] [T1Space M] (g : M → ℂ) :
  IsOpen {x : M | ∀ᶠ y in 𝓝[≠] x, g y ≠ 0} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨t, ht, hto, hxt⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hx)
  refine Filter.mem_of_superset (hto.mem_nhds hxt) fun x' hx't => ?_
  show ∀ᶠ y in 𝓝[≠] x', g y ≠ 0
  if hxx : x' = x then
    subst hxx; exact hx
  else
    refine eventually_nhdsWithin_iff.2 ?_
    filter_upwards [hto.mem_nhds hx't, isOpen_compl_singleton.mem_nhds hxx] with y hyt hyx _
    exact ht y hyt hyx
/--
[Manifold_forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Manifold_forall_eq_zero_or_forall_eventually_ne_zero_of_analyticAt_extChartAt_of_isConnected.lean)
-/
@[path]
private lemma main
  [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M] [T2Space M]
  {W : Set M}
  {g : M → ℂ}
-- given
  (hW : IsOpen W)
  (hWc : IsConnected W)
  (hg : ∀ x ∈ W, AnalyticAt ℂ (fun z : ℂ => g ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) (extChartAt 𝓘(ℂ, ℂ) x x)) :
-- imply
  (∀ x ∈ W, g x = 0) ∨ (∀ x ∈ W, ∀ᶠ y in 𝓝[≠] x, g y ≠ 0) := by
-- proof
  classical
    have key : ∀ x ∈ W, (∀ᶠ y in 𝓝 x, g y = 0) ∨ (∀ᶠ y in 𝓝[≠] x, g y ≠ 0) := by
      intro x hx
      set e := extChartAt 𝓘(ℂ, ℂ) x with he
      have hsrc : e.source ∈ 𝓝 x := extChartAt_source_mem_nhds x
      have hcont : ContinuousAt e x := continuousAt_extChartAt x
      obtain h0 | h1 := (hg x hx).eventually_eq_zero_or_eventually_ne_zero
      ·
        left
        have h0' : ∀ᶠ y in 𝓝 x, g (e.symm (e y)) = 0 := hcont.eventually h0
        filter_upwards [h0', hsrc] with y hy hys
        rwa [e.left_inv hys] at hy
      ·
        right
        have ht : Tendsto e (𝓝[≠] x) (𝓝[≠] (e x)) := by
          refine tendsto_nhdsWithin_iff.2 ⟨hcont.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
          refine eventually_nhdsWithin_iff.2 ?_
          filter_upwards [hsrc] with y hys hyx
          intro heq
          apply hyx
          calc
            _ = e.symm (e y) := (e.left_inv hys).symm
            _ = e.symm (e x) := by rw [show e y = e x from heq]
            _ = x := e.left_inv (mem_extChartAt_source x)
        have h1' : ∀ᶠ y in 𝓝[≠] x, g (e.symm (e y)) ≠ 0 := ht.eventually h1
        filter_upwards [h1', mem_nhdsWithin_of_mem_nhds hsrc] with y hy hys
        rwa [e.left_inv hys] at hy
    set u : Set M := {x | ∀ᶠ y in 𝓝 x, g y = 0} with hu
    set B : Set M := {x | ∀ᶠ y in 𝓝[≠] x, g y ≠ 0} with hB
    have huo : IsOpen u := isOpen_setOf_eventually_nhds
    have hBo : IsOpen B := isOpen_setOf_eventually_nhdsNE g
    have hcover : W ⊆ u ∪ B := fun x hx => key x hx
    if hWu : (W ∩ u).Nonempty then
      if hWB : (W ∩ B).Nonempty then
        obtain ⟨z, hzW, hzu, hzB⟩ := hWc.isPreconnected u B huo hBo hcover hWu hWB
        have := nhdsNE_neBot z
        have hzu0 : ∀ᶠ y in 𝓝 z, g y = 0 := hzu
        have hzB0 : ∀ᶠ y in 𝓝[≠] z, g y ≠ 0 := hzB
        have hzu' : ∀ᶠ y in 𝓝[≠] z, g y = 0 := mem_nhdsWithin_of_mem_nhds hzu0
        obtain ⟨y, hy1, hy2⟩ := (hzB0.and hzu').exists
        exact (hy1 hy2).elim
      else
        left
        intro x hx
        suffices hxu : x ∈ u from hxu.self_of_nhds
        obtain h | h := key x hx
        · exact h
        · exact (hWB ⟨x, hx, h⟩).elim
    else
      right
      intro x hx
      obtain h | h := key x hx
      · exact (hWu ⟨x, hx, h⟩).elim
      · exact h


-- created on 2026-10-23
