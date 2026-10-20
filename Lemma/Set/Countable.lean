import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[Complex_countable_setOf_re_gt_and_eq_zero_of_differentiableOn_of_exists_ne_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Complex_countable_setOf_re_gt_and_eq_zero_of_differentiableOn_of_exists_ne_zero.lean)
-/
@[path]
private lemma main
    (f : ℂ → ℂ) (σ : ℝ)
    (hf : DifferentiableOn ℂ f {s : ℂ | σ < s.re})
    (hne : ∃ s : ℂ, σ < s.re ∧ f s ≠ 0) :
    Set.Countable {s : ℂ | σ < s.re ∧ f s = 0} := by
  classical
  set U : Set ℂ := {s : ℂ | σ < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt (r := σ)).isPreconnected
  have hfa : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hUo
  set Z : Set ℂ := {s : ℂ | σ < s.re ∧ f s = 0} with hZ
  have hiso : ∀ z ∈ Z, ∃ ε > 0, ∀ w ∈ Metric.ball z ε, w ≠ z → f w ≠ 0 := by
    intro z hz
    have hzU : z ∈ U := hz.1
    rcases (hfa z hzU).eventually_eq_zero_or_eventually_ne_zero with h0 | h1
    ·
      exfalso
      have hEq := hfa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hzU h0
      obtain ⟨s₁, hs₁, hne₁⟩ := hne
      exact hne₁ (hEq hs₁)
    · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h1
      obtain ⟨ε, hε, hball⟩ := h1
      exact ⟨ε, hε, fun w hw hwz => hball (Metric.mem_ball.1 hw) hwz⟩
  choose ε hε hball using hiso
  have hdisj : Z.PairwiseDisjoint (fun z => if h : z ∈ Z then Metric.ball z (ε z h / 2) else ∅) := by
    intro z hz z' hz' hzz'
    dsimp only [Function.onFun]
    rw [dif_pos hz, dif_pos hz']
    refine Set.disjoint_left.2 fun w hw hw' => ?_
    have h1 : dist w z < ε z hz / 2 := Metric.mem_ball.1 hw
    have h2 : dist w z' < ε z' hz' / 2 := Metric.mem_ball.1 hw'
    rcases le_total (ε z hz) (ε z' hz') with hle | hle
    · have hmem : z ∈ Metric.ball z' (ε z' hz') := by
        rw [Metric.mem_ball]
        calc dist z z' ≤ dist z w + dist w z' := dist_triangle _ _ _
          _ = dist w z + dist w z' := by rw [dist_comm z w]
          _ < ε z hz / 2 + ε z' hz' / 2 := add_lt_add h1 h2
          _ ≤ ε z' hz' := by linarith
      exact hball z' hz' z hmem hzz' hz.2
    · have hmem : z' ∈ Metric.ball z (ε z hz) := by
        rw [Metric.mem_ball]
        calc dist z' z ≤ dist z' w + dist w z := dist_triangle _ _ _
          _ = dist w z' + dist w z := by rw [dist_comm z' w]
          _ < ε z' hz' / 2 + ε z hz / 2 := add_lt_add h2 h1
          _ ≤ ε z hz := by linarith
      exact hball z hz z' hmem (Ne.symm hzz') hz'.2
  exact hdisj.countable_of_isOpen (fun z hz => by simp only [dif_pos hz]; exact Metric.isOpen_ball)
    (fun z hz => by simp only [dif_pos hz]; exact Metric.nonempty_ball.2 (half_pos (hε z hz)))

-- created on 2026-10-20
