import Lemma.Tensor.Eq.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient
import Lemma.Real.Eq_0.Lim.of.LtAbs.IsFinite
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology


/--
Policy-gradient theorem with action values:
`γ ** Stack[t](t) @ ∇𝔼[r] = ∑' t, γ ^ t • 𝔼[Q(s[t], a[t]) • ∇ log π(a[t] | s[t])]`,
the limit `n → ∞` of `policy_gradient`: `γ ^ n • 𝔼[∇V(s[n])] → 0` by the bound `h₃`
(sympy `Sup[s[t], t] |∇V(s[t])| < ∞`, over the reachable pairs `Pr(s[t] = x) ≠ 0`).
-/
@[main]
private lemma main
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {Q : Θ → ℕ → S → A → ℝ}
  {V : Θ → ℕ → S → ℝ}
-- given
  (h₀ : ∀ t, IndepFun (r t) (fun ω (i : Fin t) => (s i ω, a i ω)) (M.traj θ))
  (h₁ : ∀ θ t x u, Q θ t x u = ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}])
  (h₂ : ∀ θ t x, V θ t x = ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M.traj θ)[|s t ⁻¹' {x}])
  (h₃ : BddAbove ((fun p : ℕ × S => ‖fderiv ℝ (fun θ => V θ p.1 p.2) θ‖) '' {p | (M.traj θ).real (s p.1 ⁻¹' {p.2}) ≠ 0}))
  (h₄ : γ ∈ Set.Ico 0 1)
  (h₅ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₆ : BddAbove (Set.range fun p : Θ × S × A => ‖fderiv ℝ (fun θ => M.pol.prob θ p.2.1 p.2.2) p.1‖)) :
-- imply
  ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M.traj θ)) θ =
    ∑' t, γ ^ t • ∫ ω, Q θ t (s t ω) (a t ω) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M.traj θ) := by
-- proof
  have h₇ := Tensor.Eq.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient h₀ h₁ h₂ h₄ h₅ h₆
  have hQ : Q = fun θ => M.Q θ γ :=
    funext fun θ => funext fun t => funext fun x => funext fun u => h₁ θ t x u
  have hV : V = fun θ => M.V θ γ := funext fun θ => funext fun t => funext fun x => h₂ θ t x
  subst hQ hV
  obtain ⟨C, hC⟩ := id h₆
  have h₈ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ C := fun θ x u => hC ⟨(θ, x, u), rfl⟩
  classical
  beta_reduce at h₇ h₃ ⊢
  obtain ⟨B, hB⟩ := h₃
  have h₉ : ∀ n, ‖∫ ω, fderiv ℝ (fun θ' => M.V θ' γ n (s n ω)) θ ∂(M.traj θ)‖ ≤ max B 0 := by
    intro n
    rw [E_s1 M θ n (fun y => fderiv ℝ (fun θ' => M.V θ' γ n y) θ)]
    calc _ ≤ ∑ y, ‖(M.traj θ).real (s n ⁻¹' {y}) • fderiv ℝ (fun θ' => M.V θ' γ n y) θ‖ :=
          norm_sum_le _ _
      _ ≤ ∑ y, (M.traj θ).real (s n ⁻¹' {y}) * max B 0 := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [norm_smul, Real.norm_of_nonneg measureReal_nonneg]
          by_cases hy : (M.traj θ).real (s n ⁻¹' {y}) = 0
          · rw [hy, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left ((hB ⟨(n, y), hy, rfl⟩).trans (le_max_left _ _))
              measureReal_nonneg
      _ = max B 0 := by rw [← Finset.sum_mul, P_sum, one_mul]
  have h₁₀ : Tendsto (fun n => γ ^ n * ‖∫ ω, fderiv ℝ (fun θ' => M.V θ' γ n (s n ω)) θ ∂(M.traj θ)‖) atTop (𝓝 0) :=
    Real.Eq_0.Lim.of.LtAbs.IsFinite (by rw [abs_of_nonneg h₄.1]; exact h₄.2)
      ⟨max B 0, by rintro _ ⟨n, rfl⟩; exact (abs_norm _).trans_le (h₉ n)⟩
  have h₁₁ : Tendsto (fun n => γ ^ n • ∫ ω, fderiv ℝ (fun θ' => M.V θ' γ n (s n ω)) θ ∂(M.traj θ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine h₁₀.congr fun n => ?_
    rw [norm_smul, norm_pow, Real.norm_of_nonneg h₄.1]
  have hq : 0 ≤ (1 - γ)⁻¹ * |M.env.R| := mul_nonneg (inv_nonneg.2 (by linarith [h₄.2])) (abs_nonneg _)
  have h₁₂ : ∀ t, ‖∫ ω, M.Q θ γ t (s t ω) (a t ω) •
      fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M.traj θ)‖ ≤
      Fintype.card A * ((1 - γ)⁻¹ * |M.env.R| * max C 0) := by
    intro t
    rw [E_score M h₅ θ t (fun y u => M.Q θ γ t y u)]
    calc _ ≤ ∑ y, ‖(M.traj θ).real (s t ⁻¹' {y}) •
          ∑ u, M.Q θ γ t y u • fderiv ℝ (fun θ' => M.pol.prob θ' y u) θ‖ := norm_sum_le _ _
      _ ≤ ∑ y, (M.traj θ).real (s t ⁻¹' {y}) * (Fintype.card A * ((1 - γ)⁻¹ * |M.env.R| * max C 0)) := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [norm_smul, Real.norm_of_nonneg measureReal_nonneg]
          refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
          calc _ ≤ ∑ u, ‖M.Q θ γ t y u • fderiv ℝ (fun θ' => M.pol.prob θ' y u) θ‖ := norm_sum_le _ _
            _ ≤ ∑ _u : A, (1 - γ)⁻¹ * |M.env.R| * max C 0 := by
                refine Finset.sum_le_sum fun u _ => ?_
                rw [norm_smul]
                exact mul_le_mul (Q_bdd M θ h₄ t y u) ((h₈ θ y u).trans (le_max_left _ _))
                  (norm_nonneg _) hq
            _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = _ := by rw [← Finset.sum_mul, P_sum, one_mul]
  have h₁₃ : Summable (fun t => γ ^ t • ∫ ω, M.Q θ γ t (s t ω) (a t ω) •
      fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M.traj θ)) := by
    have hs := (summable_geometric_of_lt_one h₄.1 h₄.2).mul_right (Fintype.card A * ((1 - γ)⁻¹ * |M.env.R| * max C 0))
    refine Summable.of_norm_bounded hs fun t => ?_
    rw [norm_smul, norm_pow, Real.norm_of_nonneg h₄.1]
    exact mul_le_mul_of_nonneg_left (h₁₂ t) (pow_nonneg h₄.1 t)
  have h₁₄ : ∀ n, ∫ ω, ∑ t ∈ Finset.range n, (γ ^ t * M.Q θ γ t (s t ω) (a t ω)) •
      fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M.traj θ) =
      ∑ t ∈ Finset.range n, γ ^ t • ∫ ω, M.Q θ γ t (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M.traj θ) := by
    intro n
    rw [integral_finsetSum _ fun t _ => integrable_sa M θ t
      (fun y u => (γ ^ t * M.Q θ γ t y u) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ)]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp_rw [mul_smul]
    exact integral_smul _ _
  have h₁₅ := h₁₃.hasSum.tendsto_sum_nat.add h₁₁
  rw [add_zero] at h₁₅
  refine tendsto_nhds_unique (tendsto_const_nhds.congr fun n => ?_) h₁₅
  rw [h₇ n, h₁₄ n]


-- created on 2026-09-26
