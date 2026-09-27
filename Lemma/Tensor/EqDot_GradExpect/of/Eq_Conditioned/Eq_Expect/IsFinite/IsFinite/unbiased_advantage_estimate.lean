import Lemma.Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.IsFinite.policy_gradient_theorem
import Lemma.Real.Eq_0.Lim.of.LtAbs.IsFinite
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology


/--
Unbiased advantage estimate: with the advantage
`A[t] = γ ** Stack[k](k) @ (r[t:] + γ * V(s[t+1:]) - V(s[t:]))`,
`γ ** Stack[t](t) @ ∇𝔼[r] = ∑' t, γ ^ t • 𝔼[A[t] • ∇ log π(a[t] | s[t])]`.
Almost surely `A[t] = γ ** Stack[k](k) @ r[t:] - V(s[t])` (telescoping with `h₃`), and the baseline
term `𝔼[V(s[t]) • ∇ log π(a[t] | s[t])]` vanishes (zero expected score).
The bounds `h₂`, `h₃` (sympy `Sup[s[t], t] |∇V| < ∞`, `Sup[s[t], t] |V| < ∞`) are over the reachable
pairs `Pr(s[t] = x) ≠ 0`.
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {V : Θ → ℕ → S → ℝ}
-- given
  (h₀ : ∀ t, IndepFun (r t) (fun ω (i : Fin t) => (s i ω, a i ω)) (M.traj θ))
  (h₁ : ∀ θ t x, V θ t x = ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x}])
  (h₂ : BddAbove ((fun p : ℕ × S => ‖fderiv ℝ (fun θ => V θ p.1 p.2) θ‖) '' {p | (M.traj θ).real (s p.1 ⁻¹' {p.2}) ≠ 0}))
  (h₃ : BddAbove ((fun p : ℕ × S => |V θ p.1 p.2|) '' {p | (M.traj θ).real (s p.1 ⁻¹' {p.2}) ≠ 0}))
  (h₄ : γ ∈ Set.Ico 0 1)
  (h₅ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₆ : BddAbove (Set.range fun p : Θ × S × A => ‖fderiv ℝ (fun θ => M.pol.prob θ p.2.1 p.2.2) p.1‖)) :
-- imply
  ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M.traj θ)) θ =
    ∑' t, γ ^ t • ∫ ω, (∑' k, γ ^ k * (r (t + k) ω + γ * V θ (t + k + 1) (s (t + k + 1) ω) -
      V θ (t + k) (s (t + k) ω))) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M.traj θ) := by
-- proof
  have hV : V = fun θ => M.V θ γ := funext fun θ => funext fun t => funext fun x => h₁ θ t x
  subst hV
  obtain ⟨C, hC⟩ := id h₆
  have h₇ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ C := fun θ x u => hC ⟨(θ, x, u), rfl⟩
  classical
  beta_reduce at h₂ h₃ ⊢
  have h₈ : BddAbove ((fun p : ℕ × S =>
      ‖∑' k, γ ^ k • fderiv ℝ (fun θ => ∫ ω, r (p.1 + k) ω ∂(M.traj θ)[|s p.1 ⁻¹' {p.2}]) θ‖) '' {p | (M.traj θ).real (s p.1 ⁻¹' {p.2}) ≠ 0}) := by
    obtain ⟨B, hB⟩ := h₂
    refine ⟨B, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    have h := hB ⟨p, hp, rfl⟩
    beta_reduce at h ⊢
    rwa [sum_grad_cond M h₅ h₇ h₄ p.1 p.2 θ hp]
  rw [Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.IsFinite.policy_gradient_theorem h₀ h₈ h₄ h₅ h₆]
  congr 1
  funext t
  congr 1
  obtain ⟨B, hB⟩ := h₃
  have h₉ : ∀ᵐ ω ∂(M.traj θ), ∑' k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
      M.V θ γ (t + k) (s (t + k) ω)) = (∑' k, γ ^ k * r (t + k) ω) - M.V θ γ t (s t ω) := by
    filter_upwards [G_hasSum M θ h₄ t, reach_ae M θ] with ω hG hR
    have hb : ∀ k, |M.V θ γ k (s k ω)| ≤ B := fun k => hB ⟨(k, s k ω), hR k, rfl⟩
    set b : ℕ → ℝ := fun k => γ ^ k * M.V θ γ (t + k) (s (t + k) ω) with hbd
    have hlim : Tendsto b atTop (𝓝 0) :=
      Real.Eq_0.Lim.of.LtAbs.IsFinite (x := fun k => M.V θ γ (t + k) (s (t + k) ω))
        (by rw [abs_of_nonneg h₄.1]; exact h₄.2) ⟨B, by rintro _ ⟨k, rfl⟩; exact hb (t + k)⟩
    have he : ∀ k, γ ^ k * (r (t + k) ω + γ * M.V θ γ (t + k + 1) (s (t + k + 1) ω) -
        M.V θ γ (t + k) (s (t + k) ω)) = γ ^ k * r (t + k) ω + (b (k + 1) - b k) := fun k => by
      simp only [hbd]
      rw [show t + (k + 1) = t + k + 1 by omega]
      ring
    have hbs : Summable (fun k => b (k + 1) - b k) := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one h₄.1 h₄.2).mul_right (2 * B))
        fun k => ?_
      calc ‖b (k + 1) - b k‖ ≤ ‖b (k + 1)‖ + ‖b k‖ := norm_sub_le _ _
        _ ≤ γ ^ k * B + γ ^ k * B := by
            simp only [hbd]
            rw [norm_mul, norm_mul, norm_pow, norm_pow, Real.norm_of_nonneg h₄.1, Real.norm_eq_abs,
              Real.norm_eq_abs]
            exact add_le_add (mul_le_mul (pow_le_pow_of_le_one h₄.1 h₄.2.le (Nat.le_succ k))
              (hb _) (abs_nonneg _) (pow_nonneg h₄.1 k)) (mul_le_mul_of_nonneg_left (hb _) (pow_nonneg h₄.1 k))
        _ = γ ^ k * (2 * B) := by ring
    have hbsum : ∑' k, (b (k + 1) - b k) = - b 0 := by
      refine tendsto_nhds_unique hbs.hasSum.tendsto_sum_nat ?_
      simp_rw [Finset.sum_range_sub]
      simpa using hlim.sub_const (b 0)
    simp_rw [he]
    rw [hG.1.summable.tsum_add hbs, hbsum]
    simp only [hbd, pow_zero, one_mul, add_zero]
    ring
  symm
  calc _ = ∫ ω, ((∑' k, γ ^ k * r (t + k) ω) - M.V θ γ t (s t ω)) •
        fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M.traj θ) :=
        integral_congr_ae (h₉.mono fun ω h => by dsimp only; rw [h])
    _ = (∫ ω, (∑' k, γ ^ k * r (t + k) ω) •
          fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M.traj θ)) -
        ∫ ω, M.V θ γ t (s t ω) •
          fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M.traj θ) := by
        simp_rw [sub_smul]
        exact integral_sub (integrable_G_smul M θ h₄ t
          (fun y u => fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ))
          (integrable_sa M θ t (fun y u => M.V θ γ t y • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ))
    _ = _ := by
        have h := E_h_score M h₅ θ t (fun y => M.V θ γ t y)
        beta_reduce at h
        rw [h, sub_zero]


-- created on 2026-09-26
