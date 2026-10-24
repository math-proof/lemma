import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IsPreconnected_exists_forall_eq_sum_zsmul_of_continuousOn_of_linearIndependent](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsPreconnected_exists_forall_eq_sum_zsmul_of_continuousOn_of_linearIndependent.lean)
-/
@[path]
private lemma main
  [TopologicalSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {k : ℕ} {S : Set X} (hS : IsPreconnected S)
  (v : Fin k → X → V) (hv : ∀ i, ContinuousOn (v i) S)
  (hlin : ∀ z ∈ S, LinearIndependent ℝ (fun i => v i z))
  (x : X → V) (hx : ContinuousOn x S)
  (hmem : ∀ z ∈ S, ∃ n : Fin k → ℤ, x z = ∑ i, n i • v i z) :
  -- imply
  ∃ n : Fin k → ℤ, ∀ z ∈ S, x z = ∑ i, n i • v i z := by
  -- proof
  classical
  have hch : ∀ z, ∃ n : Fin k → ℤ, z ∈ S → x z = ∑ i, n i • v i z := by
    intro z
    if hz : z ∈ S then
      obtain ⟨n, hn⟩ := hmem z hz
      exact ⟨n, fun _ => hn⟩
    else
      exact ⟨0, fun h => absurd h hz⟩
  choose n hn using hch
  let M : X → (Fin k → ℝ) →ₗ[ℝ] V := fun z => ∑ i, (LinearMap.proj i : (Fin k → ℝ) →ₗ[ℝ] ℝ).smulRight (v i z)
  have hM : ∀ z (c : Fin k → ℝ), M z c = ∑ i, c i • v i z := by
    intro z c
    simp [M, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_proj, Function.eval]
  have hcast : ∀ z, M z (fun i => (n z i : ℝ)) = ∑ i, n z i • v i z := by
    intro z
    rw [hM]
    simp [Int.cast_smul_eq_zsmul]
  have hMn : ∀ z ∈ S, M z (fun i => (n z i : ℝ)) = x z := fun z hz => by rw [hcast, hn z hz]
  have hloc : ∀ z₁ ∈ S, ∀ᶠ z in nhdsWithin z₁ S, n z = n z₁ := by
    intro z₁ hz₁
    have hker : LinearMap.ker (M z₁) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro c hc
      rw [hM] at hc
      apply funext fun i => Fintype.linearIndependent_iff.mp (hlin z₁ hz₁) c hc i
    obtain ⟨K, hK, hanti⟩ := (M z₁).exists_antilipschitzWith hker
    have hbound : ∀ c : Fin k → ℝ, ‖c‖ ≤ K * ‖M z₁ c‖ := fun c => hanti.le_mul_norm (map_zero _) c
    set εv : X → ℝ := fun z => ∑ i, ‖v i z₁ - v i z‖ with hεv
    set Δx : X → ℝ := fun z => ‖x z - x z₁‖ with hΔx
    have hεv_cont : ContinuousOn εv S := continuousOn_finsetSum _ fun i _ => (continuousOn_const.sub (hv i)).norm
    have hΔx_cont : ContinuousOn Δx S := (hx.sub continuousOn_const).norm
    have hεv0 : εv z₁ = 0 := by simp [hεv]
    have hΔx0 : Δx z₁ = 0 := by simp [hΔx]
    have tεv : Filter.Tendsto εv (nhdsWithin z₁ S) (nhds 0) := hεv0 ▸ hεv_cont z₁ hz₁
    have tΔx : Filter.Tendsto Δx (nhdsWithin z₁ S) (nhds 0) := hΔx0 ▸ hΔx_cont z₁ hz₁
    set n₁ : ℝ := ‖(fun i => (n z₁ i : ℝ))‖ with hn₁
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
    have e1 : ∀ᶠ z in nhdsWithin z₁ S, εv z < 1 / (2 * K) := tεv.eventually_lt_const (by positivity)
    have e2 : ∀ᶠ z in nhdsWithin z₁ S, εv z < 1 / (4 * K * (n₁ + 1)) := tεv.eventually_lt_const (by positivity)
    have e3 : ∀ᶠ z in nhdsWithin z₁ S, Δx z < 1 / (8 * K) := tΔx.eventually_lt_const (by positivity)
    have e4 : ∀ᶠ z in nhdsWithin z₁ S, z ∈ S := eventually_mem_nhdsWithin
    filter_upwards [e1, e2, e3, e4] with z h1 h2 h3 hz
    set c : Fin k → ℝ := fun i => (n z i : ℝ) - (n z₁ i : ℝ) with hc
    have hεv_nn : 0 ≤ εv z := by
      rw [hεv]
      apply Finset.sum_nonneg fun i _ => norm_nonneg _
    have hMc : M z₁ c = (x z - x z₁) + ∑ i, (n z i : ℝ) • (v i z₁ - v i z) := by
      have e : c = (fun i => (n z i : ℝ)) - (fun i => (n z₁ i : ℝ)) := rfl
      rw [e, map_sub, hMn z₁ hz₁, ← hMn z hz, hM, hM]
      simp only [smul_sub, Finset.sum_sub_distrib]
      abel
    have hn_le : ‖(fun i => (n z i : ℝ))‖ ≤ ‖c‖ + n₁ := by
      have : (fun i => (n z i : ℝ)) = c + (fun i => (n z₁ i : ℝ)) := by
        funext i
        simp [hc]
      rw [this]
      apply norm_add_le _ _
    have hsum : ‖∑ i, (n z i : ℝ) • (v i z₁ - v i z)‖ ≤ ‖(fun i => (n z i : ℝ))‖ * εv z := by
      rw [hεv, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_smul]
      apply mul_le_mul_of_nonneg_right (norm_le_pi_norm (fun i => (n z i : ℝ)) i) (norm_nonneg _)
    have hc_le : ‖c‖ ≤ K * (Δx z + (‖c‖ + n₁) * εv z) := calc
      _ ≤ K * ‖M z₁ c‖ := hbound c
      _ ≤ K * (Δx z + ‖(fun i => (n z i : ℝ))‖ * εv z) := by
        gcongr
        rw [hMc]
        apply (norm_add_le _ _).trans (add_le_add le_rfl hsum)
      _ ≤ K * (Δx z + (‖c‖ + n₁) * εv z) := by
        gcongr
    have hKε : K * εv z ≤ 1 / 2 := by
      have h1' : εv z * (2 * K) < 1 := by
        rwa [lt_div_iff₀ (by positivity)] at h1
      nlinarith [h1', hKpos, hεv_nn]
    have hn₁nn : 0 ≤ n₁ := norm_nonneg _
    have hKn₁ε : K * (n₁ * εv z) ≤ 1 / 4 := by
      have h2' : εv z * (4 * K * (n₁ + 1)) < 1 := by
        rwa [lt_div_iff₀ (by positivity)] at h2
      nlinarith [hεv_nn, hn₁nn, hKpos]
    have hΔnn : 0 ≤ Δx z := by
      rw [hΔx]
      apply norm_nonneg _
    have hKΔ : K * Δx z < 1 / 8 := by
      have h3' : Δx z * (8 * K) < 1 := by
        rwa [lt_div_iff₀ (by positivity)] at h3
      nlinarith [h3', hKpos, hΔnn]
    have hc1 : ‖c‖ < 1 := by
      nlinarith [hc_le, hKε, hKn₁ε, hKΔ, norm_nonneg c, hεv_nn]
    funext i
    have hi : ‖c i‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm c i) hc1
    have hi' : |((n z i : ℝ) - (n z₁ i : ℝ))| < 1 := by
      rw [hc, Real.norm_eq_abs] at hi
      apply hi
    have hi'' : |n z i - n z₁ i| < 1 := by
      exact_mod_cast hi'
    rw [Int.abs_lt_one_iff, sub_eq_zero] at hi''
    apply hi''
  let _ : DiscreteTopology (Fin k → ℤ) := inferInstance
  have hcont : ContinuousOn n S := fun z₁ hz₁ => (tendsto_const_nhds.congr' ((hloc z₁ hz₁).mono fun z hz => hz.symm))
  if hSe : S = ∅ then
    refine ⟨0, fun z hz => ?_⟩
    rw [hSe] at hz
    apply absurd hz (Set.notMem_empty _)
  else
    obtain ⟨z₀, hz₀⟩ := Set.nonempty_iff_ne_empty.mpr hSe
    refine ⟨n z₀, fun z hz => ?_⟩
    rw [← hS.constant hcont hz hz₀]
    apply hn z hz


-- created on 2026-10-20
