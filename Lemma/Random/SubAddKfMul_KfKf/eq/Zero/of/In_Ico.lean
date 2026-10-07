import sympy.stats.policy_trajectory.advantage
import sympy.Basic
open MeasureTheory ProbabilityTheory Finset Filter Topology PolicyGradient PolicyGradient.Model


/--
Bellman identity for the kernel expectations: the one-step expected residual
`Kf rc 1 z + γ * Kf (Vc ∘ state) 2 z - Kf (Vc ∘ state) 1 z` vanishes.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {γ : ℝ}
-- given
  (θ : Θ)
  (h₀ : γ ∈ Set.Ico 0 1)
  (z : ℝ × S × A) :
-- imply
  M.Kf θ M.rc 1 z + γ * M.Kf θ (fun w => M.Vc θ γ w.2.1) 2 z -
    M.Kf θ (fun w => M.Vc θ γ w.2.1) 1 z = 0 := by
-- proof
  have hf : StronglyMeasurable (fun w : ℝ × S × A => M.Vc θ γ w.2.1) :=
    (disc_sm (M.Vc θ γ)).comp_measurable measurable_snd.fst
  have hC : ∀ w : ℝ × S × A, ‖(fun w : ℝ × S × A => M.Vc θ γ w.2.1) w‖ ≤ ∑ y', ‖M.Vc θ γ y'‖ :=
    fun w => h_bdd (M.Vc θ γ) w.2.1
  have w0 : ∀ y, M.W θ (fun w : ℝ × S × A => M.Vc θ γ w.2.1) 0 y = M.Vc θ γ y :=
    W_fst_zero M θ (M.Vc θ γ)
  have w1 : ∀ y, M.W θ (fun w : ℝ × S × A => M.Vc θ γ w.2.1) 1 y =
      ∑ u, M.pol.prob θ y u * ∑ y', M.T y u y' * M.Vc θ γ y' := fun y => by
    show M.W θ (fun w : ℝ × S × A => M.Vc θ γ w.2.1) (0 + 1) y = _
    rw [W_succ M θ hf hC 0 y]
    simp_rw [w0]
  have e1 := Kf_succ M θ (rc_sm M) (rc_bdd M) 0 z
  have e2 := Kf_succ M θ hf hC 1 z
  have e3 := Kf_succ M θ hf hC 0 z
  show M.Kf θ M.rc (0 + 1) z + γ * M.Kf θ (fun w => M.Vc θ γ w.2.1) (1 + 1) z -
      M.Kf θ (fun w => M.Vc θ γ w.2.1) (0 + 1) z = 0
  rw [e1, e2, e3]
  simp_rw [w0, w1]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  have hrec : M.Vc θ γ y = M.W θ M.rc 0 y +
      γ * ∑ u, M.pol.prob θ y u * ∑ y', M.T y u y' * M.Vc θ γ y' := v_closed M θ h₀ y
  rw [hrec]
  ring


-- created on 2026-10-06
