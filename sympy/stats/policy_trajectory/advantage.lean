import sympy.stats.policy_trajectory.gradient

/-!
# Zero-mean property of the temporal-difference residuals (generalized advantage estimation)

With the time-free value function `Vc` (`= M.V` at reachable states, `V_eq_Vc`), the residual
`δ[j] = r[j] + γ * Vc(s[j+1]) - Vc(s[j])` is orthogonal to every function of the earlier pair
`(s[t], a[t])`, `t < j`: `𝔼[δ[j] • ψ(s[t], a[t])] = 0` (`E_delta_psi`).  This follows from the Markov
property along histories (`hist_iter`) and the Bellman equation `Vc = W rc 0 + γ * ∑ π T Vc`
(`Kf_delta`).  Consequently, for every `c ∈ [0, 1)`,
`𝔼[(∑' k, c ^ k * δ[t + k]) • ψ(s[t], a[t])] = 𝔼[δ[t] • ψ(s[t], a[t])]` (`E_sum_delta`);
the weight `c = γ * λ` gives the generalized advantage estimator (GAE).

No `Lemma.*` module is imported here.
-/
open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace PolicyGradient

namespace Model

variable {Θ S A : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem Vc_bdd (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) (x : S) :
    ‖M.Vc θ γ x‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
  unfold Model.Vc
  refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hγ.1 hγ.2).mul_right _) fun k => ?_
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hγ.1]
  exact mul_le_mul_of_nonneg_left (W_bdd M θ k x) (pow_nonneg hγ.1 k)

/-- the bound of the temporal-difference residual `δ[j] = r[j] + γ * V(s[j+1]) - V(s[j])` -/
noncomputable def deltaBound (M : Model Θ S A) (γ : ℝ) : ℝ :=
  |M.env.R| + γ * ((1 - γ)⁻¹ * |M.env.R|) + (1 - γ)⁻¹ * |M.env.R|

omit [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A] in
theorem delta_meas (V : S → ℝ) (γ : ℝ) (j : ℕ) :
    Measurable (fun ω : ℕ → S × A × ℝ => r j ω + γ * V (s (j + 1) ω) - V (s j ω)) :=
  ((r_meas j).add (((measurable_of_countable V).comp (s_meas (j + 1))).const_mul γ)).sub
    ((measurable_of_countable V).comp (s_meas j))

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem delta_ae_bdd (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) :
    ∀ᵐ ω ∂(M.traj θ), ∀ j, ‖r j ω + γ * M.Vc θ γ (s (j + 1) ω) - M.Vc θ γ (s j ω)‖ ≤
      M.deltaBound γ := by
  filter_upwards [r_bdd_ae M θ] with ω hr j
  calc _ ≤ ‖r j ω‖ + ‖γ * M.Vc θ γ (s (j + 1) ω)‖ + ‖M.Vc θ γ (s j ω)‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ M.deltaBound γ := by
        rw [norm_mul, Real.norm_of_nonneg hγ.1]
        exact add_le_add (add_le_add (hr j) (mul_le_mul_of_nonneg_left (Vc_bdd M θ hγ _) hγ.1))
          (Vc_bdd M θ hγ _)

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
/-- almost surely the `c`-discounted sums of residuals are bounded, uniformly in `t` -/
theorem delta_sum_bdd (M : Model Θ S A) (θ : Θ) {γ c : ℝ} (hγ : γ ∈ Set.Ico 0 1)
    (hc : c ∈ Set.Ico 0 1) :
    ∀ᵐ ω ∂(M.traj θ), ∀ t, ‖∑' k, c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) -
      M.Vc θ γ (s (t + k) ω))‖ ≤ (1 - c)⁻¹ * M.deltaBound γ := by
  filter_upwards [delta_ae_bdd M θ hγ] with ω h t
  refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hc.1 hc.2).mul_right _) fun k => ?_
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hc.1]
  exact mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg hc.1 k)

omit [DecidableEq S] [DecidableEq A] in
theorem Kf_delta (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) (z : S × A × ℝ) :
    M.Kf θ M.rc 1 z + γ * M.Kf θ (fun w => M.Vc θ γ w.1) 2 z -
      M.Kf θ (fun w => M.Vc θ γ w.1) 1 z = 0 := by
  have hf : StronglyMeasurable (fun w : S × A × ℝ => M.Vc θ γ w.1) :=
    (disc_sm (M.Vc θ γ)).comp_measurable measurable_fst
  have hC : ∀ w : S × A × ℝ, ‖(fun w : S × A × ℝ => M.Vc θ γ w.1) w‖ ≤ ∑ y', ‖M.Vc θ γ y'‖ :=
    fun w => h_bdd (M.Vc θ γ) w.1
  have w0 : ∀ y, M.W θ (fun w : S × A × ℝ => M.Vc θ γ w.1) 0 y = M.Vc θ γ y :=
    W_fst_zero M θ (M.Vc θ γ)
  have w1 : ∀ y, M.W θ (fun w : S × A × ℝ => M.Vc θ γ w.1) 1 y =
      ∑ u, M.pol.prob θ y u * ∑ y', M.T y u y' * M.Vc θ γ y' := fun y => by
    show M.W θ (fun w : S × A × ℝ => M.Vc θ γ w.1) (0 + 1) y = _
    rw [W_succ M θ hf hC 0 y]
    simp_rw [w0]
  have e1 := Kf_succ M θ (rc_sm M) (rc_bdd M) 0 z
  have e2 := Kf_succ M θ hf hC 1 z
  have e3 := Kf_succ M θ hf hC 0 z
  show M.Kf θ M.rc (0 + 1) z + γ * M.Kf θ (fun w => M.Vc θ γ w.1) (1 + 1) z -
      M.Kf θ (fun w => M.Vc θ γ w.1) (0 + 1) z = 0
  rw [e1, e2, e3]
  simp_rw [w0, w1]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun y _ => ?_
  have hrec : M.Vc θ γ y = M.W θ M.rc 0 y +
      γ * ∑ u, M.pol.prob θ y u * ∑ y', M.T y u y' * M.Vc θ γ y' := v_closed M θ hγ y
  rw [hrec]
  ring

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem int_hist_mul (M : Model Θ S A) (θ : Θ) (n k : ℕ) {G : (Π _ : Iic n, S × A × ℝ) → ℝ}
    (hG : StronglyMeasurable G) {CG : ℝ} (hCG : ∀ h, ‖G h‖ ≤ CG)
    {g : S × A × ℝ → ℝ} (hg : StronglyMeasurable g) {C : ℝ} (hC : ∀ z, ‖g z‖ ≤ C) :
    Integrable (fun ω => G (Preorder.frestrictLe n ω) * g (ω k)) (M.traj θ) := by
  refine Integrable.of_bound (C := CG * C) ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact ((hG.comp_measurable (Preorder.measurable_frestrictLe n)).mul
      (hg.comp_measurable (measurable_pi_apply k))).aestronglyMeasurable
  · rw [norm_mul]
    exact mul_le_mul (hCG _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hCG (Preorder.frestrictLe n ω)))

omit [DecidableEq S] [DecidableEq A] in
theorem integrable_delta_smul (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (t j : ℕ) (ψ : S → A → E) :
    Integrable (fun ω => (r j ω + γ * M.Vc θ γ (s (j + 1) ω) - M.Vc θ γ (s j ω)) •
      ψ (s t ω) (a t ω)) (M.traj θ) := by
  have hX : Measurable (fun ω : ℕ → S × A × ℝ => (s t ω, a t ω)) := (s_meas t).prodMk (a_meas t)
  refine Integrable.of_bound (C := M.deltaBound γ * ∑ p : S × A, ‖ψ p.1 p.2‖)
    ((delta_meas (M.Vc θ γ) γ j).stronglyMeasurable.smul
      ((StronglyMeasurable.of_discrete (f := fun p : S × A => ψ p.1 p.2)).comp_measurable
        hX)).aestronglyMeasurable ?_
  filter_upwards [delta_ae_bdd M θ hγ] with ω h
  rw [norm_smul]
  exact mul_le_mul (h j) (Finset.single_le_sum (f := fun p : S × A => ‖ψ p.1 p.2‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ (s t ω, a t ω))) (norm_nonneg _)
    ((norm_nonneg _).trans (h j))

theorem E_ind_delta (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) (t n : ℕ)
    (htn : t ≤ n) (x : S) (u : A) :
    ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
      (r (n + 1) ω + γ * M.Vc θ γ (s (n + 1 + 1) ω) - M.Vc θ γ (s (n + 1) ω)) ∂(M.traj θ) = 0 := by
  let Gh : (Π _ : Iic n, S × A × ℝ) → ℝ := fun h =>
    if (h ⟨t, mem_Iic.2 htn⟩).1 = x ∧ (h ⟨t, mem_Iic.2 htn⟩).2.1 = u then (1:ℝ) else 0
  have hG : StronglyMeasurable Gh :=
    (disc_sm (fun p : S × A => if p.1 = x ∧ p.2 = u then (1:ℝ) else 0)).comp_measurable
      ((measurable_fst.comp (measurable_pi_apply _)).prodMk
        (measurable_fst.comp (measurable_snd.comp (measurable_pi_apply _))))
  have hCG : ∀ h, ‖Gh h‖ ≤ 1 := fun h => by dsimp only [Gh]; split_ifs <;> simp
  have hGω : ∀ ω : ℕ → S × A × ℝ, Gh (Preorder.frestrictLe n ω) =
      (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) := fun ω => rfl
  let f : S × A × ℝ → ℝ := fun w => M.Vc θ γ w.1
  have hf : StronglyMeasurable f := (disc_sm (M.Vc θ γ)).comp_measurable measurable_fst
  have hC : ∀ w, ‖f w‖ ≤ ∑ y', ‖M.Vc θ γ y'‖ := fun w => h_bdd (M.Vc θ γ) w.1
  have h1 := hist_iter M θ (rc_sm M) (rc_bdd M) 1 n hG hCG
  have h2 := hist_iter M θ hf hC 2 n hG hCG
  have h3 := hist_iter M θ hf hC 1 n hG hCG
  have i1 := int_hist_mul M θ n (n + 1) hG hCG (rc_sm M) (rc_bdd M)
  have i2 := int_hist_mul M θ n (n + 2) hG hCG hf hC
  have i3 := int_hist_mul M θ n (n + 1) hG hCG hf hC
  have k1 := Kf_bdd M θ (rc_sm M) (rc_bdd M) 1
  have k2 := Kf_bdd M θ hf hC 2
  have k3 := Kf_bdd M θ hf hC 1
  have j1 := int_hist_mul M θ n n hG hCG k1.1 k1.2
  have j2 := int_hist_mul M θ n n hG hCG k2.1 k2.2
  have j3 := int_hist_mul M θ n n hG hCG k3.1 k3.2
  have hae : ∀ᵐ ω ∂(M.traj θ),
      (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
        (r (n + 1) ω + γ * M.Vc θ γ (s (n + 1 + 1) ω) - M.Vc θ γ (s (n + 1) ω)) =
      Gh (Preorder.frestrictLe n ω) * M.rc (ω (n + 1)) +
        γ * (Gh (Preorder.frestrictLe n ω) * f (ω (n + 2))) -
        Gh (Preorder.frestrictLe n ω) * f (ω (n + 1)) := by
    filter_upwards [r_ae M θ (n + 1)] with ω hω
    rw [hGω, hω]
    show _ * (M.rc (ω (n + 1)) + γ * M.Vc θ γ (ω (n + 2)).1 - M.Vc θ γ (ω (n + 1)).1) = _
    ring
  have hz : ∀ ω : ℕ → S × A × ℝ, Gh (Preorder.frestrictLe n ω) * M.Kf θ M.rc 1 (ω n) +
      γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ f 2 (ω n)) -
      Gh (Preorder.frestrictLe n ω) * M.Kf θ f 1 (ω n) = 0 := fun ω => by
    have := Kf_delta M θ hγ (ω n)
    calc _ = Gh (Preorder.frestrictLe n ω) *
        (M.Kf θ M.rc 1 (ω n) + γ * M.Kf θ f 2 (ω n) - M.Kf θ f 1 (ω n)) := by ring
      _ = 0 := by rw [this, mul_zero]
  have i23 : Integrable (fun ω => γ * (Gh (Preorder.frestrictLe n ω) * f (ω (n + 2)))) (M.traj θ) :=
    i2.const_mul γ
  have j23 : Integrable (fun ω => γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ f 2 (ω n))) (M.traj θ) :=
    j2.const_mul γ
  have ia : Integrable (fun ω => Gh (Preorder.frestrictLe n ω) * M.rc (ω (n + 1)) +
      γ * (Gh (Preorder.frestrictLe n ω) * f (ω (n + 2)))) (M.traj θ) := i1.add i23
  have ja : Integrable (fun ω => Gh (Preorder.frestrictLe n ω) * M.Kf θ M.rc 1 (ω n) +
      γ * (Gh (Preorder.frestrictLe n ω) * M.Kf θ f 2 (ω n))) (M.traj θ) := j1.add j23
  rw [integral_congr_ae hae, integral_sub ia i3, integral_add i1 i23, integral_const_mul,
    h1, h2, h3]
  have e := integral_sub ja j3
  rw [integral_add j1 j23, integral_const_mul] at e
  rw [← e]
  simp_rw [hz]
  simp

/-- `𝔼[δ[n+1] • ψ(s[t], a[t])] = 0` for `t ≤ n` -/
theorem E_delta_psi (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) (t n : ℕ)
    (htn : t ≤ n) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ψ : S → A → E) :
    ∫ ω, (r (n + 1) ω + γ * M.Vc θ γ (s (n + 1 + 1) ω) - M.Vc θ γ (s (n + 1) ω)) •
      ψ (s t ω) (a t ω) ∂(M.traj θ) = 0 := by
  have hI : ∀ x u, Integrable (fun ω => (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
      (r (n + 1) ω + γ * M.Vc θ γ (s (n + 1 + 1) ω) - M.Vc θ γ (s (n + 1) ω))) (M.traj θ) := by
    intro x u
    refine (integrable_delta_smul M θ hγ t (n + 1)
      (fun x' u' => if x' = x ∧ u' = u then (1:ℝ) else 0)).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    simp only [smul_eq_mul]
    ring
  have e : (fun ω => (r (n + 1) ω + γ * M.Vc θ γ (s (n + 1 + 1) ω) - M.Vc θ γ (s (n + 1) ω)) •
      ψ (s t ω) (a t ω)) = fun ω => ∑ x, ∑ u, ((if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
        (r (n + 1) ω + γ * M.Vc θ γ (s (n + 1 + 1) ω) - M.Vc θ γ (s (n + 1) ω))) • ψ x u :=
    funext fun ω => ind_smul_sum t ω _ ψ
  rw [e, integral_finsetSum _ fun x _ => integrable_finsetSum _ fun u _ => (hI x u).smul_const _]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [integral_finsetSum _ fun u _ => (hI x u).smul_const _]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [integral_smul_const, E_ind_delta M θ hγ t n htn x u, zero_smul]

/-- the `c`-discounted sum of the residuals against a function of `(s[t], a[t])` is the first term -/
theorem E_sum_delta (M : Model Θ S A) (θ : Θ) {γ c : ℝ} (hγ : γ ∈ Set.Ico 0 1)
    (hc : c ∈ Set.Ico 0 1) (t : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (ψ : S → A → E) :
    ∫ ω, (∑' k, c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) -
        M.Vc θ γ (s (t + k) ω))) • ψ (s t ω) (a t ω) ∂(M.traj θ) =
      ∫ ω, (r t ω + γ * M.Vc θ γ (s (t + 1) ω) - M.Vc θ γ (s t ω)) • ψ (s t ω) (a t ω)
        ∂(M.traj θ) := by
  classical
  let F : ℕ → (ℕ → S × A × ℝ) → E := fun k ω =>
    (c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) - M.Vc θ γ (s (t + k) ω))) •
      ψ (s t ω) (a t ω)
  have hF : ∀ k ω, F k ω = c ^ k • ((r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) -
      M.Vc θ γ (s (t + k) ω)) • ψ (s t ω) (a t ω)) := fun k ω => by
    simp only [F, mul_smul]
  have hFi : ∀ k, Integrable (F k) (M.traj θ) := fun k => by
    have := (integrable_delta_smul M θ hγ t (t + k) ψ).smul (c ^ k)
    exact this.congr (Filter.Eventually.of_forall fun ω => (hF k ω).symm)
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℝ, Ψ = ∑ p : S × A, ‖ψ p.1 p.2‖ := ⟨_, rfl⟩
  have hFb : ∀ k, ∀ᵐ ω ∂(M.traj θ), ‖F k ω‖ ≤ c ^ k * (M.deltaBound γ * Ψ) := fun k => by
    filter_upwards [delta_ae_bdd M θ hγ] with ω h
    rw [hF, norm_smul, norm_smul, norm_pow, Real.norm_of_nonneg hc.1, hΨ]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hc.1 k)
    exact mul_le_mul (h _) (Finset.single_le_sum (f := fun p : S × A => ‖ψ p.1 p.2‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (s t ω, a t ω))) (norm_nonneg _)
      ((norm_nonneg _).trans (h 0))
  have hsum : Summable (fun k => ∫ ω, ‖F k ω‖ ∂(M.traj θ)) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one hc.1 hc.2).mul_right (M.deltaBound γ * Ψ))
    calc _ ≤ ∫ _, c ^ k * (M.deltaBound γ * Ψ) ∂(M.traj θ) :=
          integral_mono_ae (hFi k).norm (integrable_const _) (hFb k)
      _ = c ^ k * (M.deltaBound γ * Ψ) := by simp
  have hHas := hasSum_integral_of_summable_integral_norm hFi hsum
  have hzero : ∀ k, k ≠ 0 → ∫ ω, F k ω ∂(M.traj θ) = 0 := by
    intro k hk
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    simp_rw [hF]
    rw [integral_smul]
    have := E_delta_psi M θ hγ t (t + k') (Nat.le_add_right t k') ψ
    rw [show (fun ω => (r (t + k'.succ) ω + γ * M.Vc θ γ (s (t + k'.succ + 1) ω) -
        M.Vc θ γ (s (t + k'.succ) ω)) • ψ (s t ω) (a t ω)) = fun ω => (r (t + k' + 1) ω +
        γ * M.Vc θ γ (s (t + k' + 1 + 1) ω) - M.Vc θ γ (s (t + k' + 1) ω)) • ψ (s t ω) (a t ω)
        from rfl, this, smul_zero]
  have h0 : ∑' k, ∫ ω, F k ω ∂(M.traj θ) = ∫ ω, F 0 ω ∂(M.traj θ) := tsum_eq_single 0 hzero
  have hae : ∀ᵐ ω ∂(M.traj θ), (∑' k, c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) -
        M.Vc θ γ (s (t + k) ω))) • ψ (s t ω) (a t ω) = ∑' k, F k ω := by
    filter_upwards [delta_ae_bdd M θ hγ] with ω h
    have hs : Summable (fun k => c ^ k * (r (t + k) ω + γ * M.Vc θ γ (s (t + k + 1) ω) -
        M.Vc θ γ (s (t + k) ω))) := by
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hc.1 hc.2).mul_right
        (M.deltaBound γ)) fun k => ?_
      rw [norm_mul, norm_pow, Real.norm_of_nonneg hc.1]
      exact mul_le_mul_of_nonneg_left (h _) (pow_nonneg hc.1 k)
    exact (hs.tsum_smul_const _).symm
  rw [integral_congr_ae hae, ← hHas.tsum_eq, h0]
  simp [F]

end Model

end PolicyGradient
