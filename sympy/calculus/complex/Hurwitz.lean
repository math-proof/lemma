import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Hurwitz theorem: zero-free dichotomy for locally uniform limits (N327)

Let `F : α → ℂ → ℂ` converge locally uniformly on an open preconnected
set `U` to `f`, with each `F n` eventually holomorphic and zero-free on
`U`. Then either `f` vanishes identically on `U` or `f` is zero-free on
`U`. The witness corollary upgrades a single nonzero value of `f` inside
`U` to global zero-freeness on `U`.

The proof is Hurwitz's theorem. The limit is holomorphic by Mathlib's
locally uniform limit theorem. If `f` is neither identically zero nor
zero-free, pick a zero `z₀` and a point where `f` is nonzero; the
isolated-zero principle gives a closed ball around `z₀` inside `U` with
`f` nonzero on the punctured ball. The norm of `f` attains a positive
minimum `m` on the sphere. One approximant is uniformly within `m / 4`
of `f` on the closed ball, so it stays at distance at least `m / 2`
from its center value on the sphere. If the approximant is nonconstant
near `z₀`, `DiffContOnCl.ball_subset_image_closedBall` forces `0` into
its image, against zero-freeness; if it is locally constant, the
identity principle makes it globally constant and the triangle
inequality at the minimum point gives a contradiction.
-/

open Filter Metric Set
open scoped Topology

variable {α : Type*} {F : α → ℂ → ℂ} {f : ℂ → ℂ}
  {φ : Filter α} {U : Set ℂ}

theorem TendstoLocallyUniformlyOn.eqOn_zero_or_ne_zero [φ.NeBot]
    (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U)
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hF_ne : ∀ᶠ n in φ, ∀ z ∈ U, F n z ≠ 0) :
    Set.EqOn f 0 U ∨ ∀ z ∈ U, f z ≠ 0 := by
  have hfDiff : DifferentiableOn ℂ f U := hf.differentiableOn hF hU
  have hfAn : AnalyticOnNhd ℂ f U := hfDiff.analyticOnNhd hU
  by_cases h0 : Set.EqOn f 0 U
  · exact Or.inl h0
  · right
    obtain ⟨w, hwU, hw0⟩ : ∃ x ∈ U, f x ≠ 0 := by
      by_contra hall
      push Not at hall
      exact h0 (fun x hx => by simpa using hall x hx)
    intro z₀ hz₀ hzero
    have hloc : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 := by
      rcases (hfAn z₀ hz₀).eventually_eq_zero_or_eventually_ne_zero with h1
        | h2
      · exfalso
        apply h0
        apply hfAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hz₀
        filter_upwards [h1] with z hz
        simpa using hz
      · exact h2
    have hUev : {z | z ∈ U ∧ (z ≠ z₀ → f z ≠ 0)} ∈ 𝓝 z₀ := by
      filter_upwards [hU.mem_nhds hz₀,
        eventually_nhdsWithin_iff.mp hloc] with z hzU hzne
      exact ⟨hzU, fun hne => hzne hne⟩
    obtain ⟨r, hr0, hrsub⟩ : ∃ r > 0, closedBall z₀ r ⊆
      {z | z ∈ U ∧ (z ≠ z₀ → f z ≠ 0)} := by
      simpa using nhds_basis_closedBall.mem_iff.mp hUev
    have hsubU : closedBall z₀ r ⊆ U := fun z hz => (hrsub hz).1
    have hne : ∀ z ∈ closedBall z₀ r, z ≠ z₀ → f z ≠ 0 :=
      fun z hz hnez => (hrsub hz).2 hnez
    have hsph : (sphere z₀ r).Nonempty :=
      NormedSpace.sphere_nonempty.mpr hr0.le
    have hcont : ContinuousOn (fun x => ‖f x‖) (sphere z₀ r) :=
      continuous_norm.comp_continuousOn
        (hfDiff.continuousOn.mono (sphere_subset_closedBall.trans hsubU))
    obtain ⟨x, hxs, hxmin⟩ :=
      (isCompact_sphere z₀ r).exists_isMinOn hsph hcont
    have hxne : x ≠ z₀ := ne_of_mem_sphere hxs hr0.ne.symm
    have hxm : 0 < ‖f x‖ :=
      norm_pos_iff.mpr (hne x (sphere_subset_closedBall hxs) hxne)
    have hUball : TendstoUniformlyOn F f φ (closedBall z₀ r) :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hf _
        hsubU (isCompact_closedBall z₀ r)
    have hclose : ∀ᶠ n in φ, ∀ z ∈ closedBall z₀ r,
        dist (f z) (F n z) < ‖f x‖ / 4 :=
      Metric.tendstoUniformlyOn_iff.mp hUball _ (by positivity)
    obtain ⟨n, ⟨hnD, hn0⟩, hnclose⟩ := (hF.and hF_ne).and hclose |>.exists
    have hcenter : ‖F n z₀‖ < ‖f x‖ / 4 := by
      have hmem : z₀ ∈ closedBall z₀ r := mem_closedBall_self hr0.le
      simpa [hzero, dist_eq_norm] using hnclose z₀ hmem
    have hsep : ∀ z ∈ sphere z₀ r, ‖f x‖ / 2 ≤ ‖F n z - F n z₀‖ := by
      intro z hz
      have h1 : ‖f x‖ ≤ ‖f z‖ := hxmin hz
      have h2 : ‖f z - F n z‖ < ‖f x‖ / 4 := by
        have h2' := hnclose z (sphere_subset_closedBall hz)
        rwa [dist_eq_norm] at h2'
      have t1 : ‖f z‖ - ‖F n z₀‖ ≤ ‖f z - F n z₀‖ := norm_sub_norm_le _ _
      have t2 : ‖f z - F n z₀‖ ≤ ‖f z - F n z‖ + ‖F n z - F n z₀‖ := by
        have he : f z - F n z₀ = (f z - F n z) + (F n z - F n z₀) := by
          abel
        rw [he]
        exact norm_add_le _ _
      linarith
    rcases (hnD.analyticAt (hU.mem_nhds hz₀)).eventually_eq_or_eventually_ne
      analyticAt_const with hconst | hfreq
    · have hgAn : AnalyticOnNhd ℂ (F n) U := hnD.analyticOnNhd hU
      have hglob : Set.EqOn (F n) (fun _ => F n z₀) U :=
        hgAn.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hUc
          hz₀ (by filter_upwards [hconst] with z hz; simpa using hz)
      have hxx : F n x = F n z₀ := hglob (hsubU (sphere_subset_closedBall hxs))
      have hxclose : ‖f x - F n z₀‖ < ‖f x‖ / 4 := by
        have hx' := hnclose x (sphere_subset_closedBall hxs)
        rwa [dist_eq_norm, hxx] at hx'
      have tri : ‖f x‖ ≤ ‖f x - F n z₀‖ + ‖F n z₀‖ := by
        have he : f x = (f x - F n z₀) + F n z₀ := by abel
        conv_lhs => rw [he]
        exact norm_add_le _ _
      linarith
    · have hfreq' : ∃ᶠ z in 𝓝 z₀, F n z ≠ F n z₀ := by
        have hfreq2 : ∀ᶠ z in 𝓝[≠] z₀, F n z ≠ F n z₀ := by
          simpa using hfreq
        exact hfreq2.frequently.filter_mono nhdsWithin_le_nhds
      have hD : DiffContOnCl ℂ (F n) (ball z₀ r) := by
        refine ⟨hnD.mono (ball_subset_closedBall.trans hsubU), ?_⟩
        rw [closure_ball z₀ hr0.ne.symm]
        exact hnD.continuousOn.mono hsubU
      have himg := hD.ball_subset_image_closedBall hr0 hsep hfreq'
      have h0mem : (0 : ℂ) ∈ ball (F n z₀) (‖f x‖ / 2 / 2) := by
        rw [mem_ball, dist_comm, dist_zero_right]
        linarith [hcenter]
      obtain ⟨y, hyball, hy0⟩ := himg h0mem
      exact hn0 y (hsubU hyball) hy0

theorem TendstoLocallyUniformlyOn.ne_zero_of_exists_ne_zero [φ.NeBot]
    (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U)
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hF_ne : ∀ᶠ n in φ, ∀ z ∈ U, F n z ≠ 0)
    (hf_ne : ∃ z ∈ U, f z ≠ 0) :
    ∀ z ∈ U, f z ≠ 0 := by
  rcases hf.eqOn_zero_or_ne_zero hF hU hUc hF_ne with h0 | hne
  · obtain ⟨z, hzU, hzf⟩ := hf_ne
    exact absurd (by simpa using h0 hzU) hzf
  · exact hne
