import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint
import Lemma.Random.Integrable_Mul_R.of.Measurable
import Lemma.Random.Integral.eq.MulMulRealPreimageProbIntegral_MulEqAndEq.of.All_Eq
import Lemma.Random.Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico
import Lemma.Random.Integral_MulEqAndEq.eq.MulMulRealPreimageProbIntegral_Rc.of.All_Eq
import Lemma.Random.Integral_MulEqAndEq.eq.MulMulRealProbSum_MulTW.of.All_Eq
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


private lemma E_ind_r
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (M : Model Θ S A)
  (θ : Θ)
  (t k : ℕ)
  (x : S)
  (u : A) :
  ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * r (t + k) ω ∂(M θ) =
    ((M θ).real (s t ⁻¹' {x}) * M.policy.prob θ x u) *
    ∫ ω, r (t + k) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] := by
  if h : (M θ).real (s t ⁻¹' {x}) * M.policy.prob θ x u = 0 then
    rw [h, zero_mul]
    cases k with
    | zero => rw [add_zero, Integral_MulEqAndEq.eq.MulMulRealPreimageProbIntegral_Rc.of.All_Eq h₁, h, zero_mul]
    | succ j => rw [Integral_MulEqAndEq.eq.MulMulRealProbSum_MulTW.of.All_Eq h₁, h, zero_mul]
  else
    rw [Integral.eq.MulMulRealPreimageProbIntegral_MulEqAndEq.of.All_Eq h₁, mul_inv_cancel_left₀ h]

/--
`𝔼[1{s[t] = x ∧ a[t] = u} * G[t]] = ℙ(s[t] = x) * π_θ(u | x) * Q θ γ t x u`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (u : A) :
-- imply
  let Q (θ : Θ) (t : ℕ) (x : S) (u : A) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u);
  ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω ∂(M θ) =
    ((M θ).real (s t ⁻¹' {x}) * M.policy.prob θ x u) * Q θ t x u := by
-- proof
  set G := (γ ^ (id : ℕ → ℕ)) @ r[t:]
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  let Q (θ : Θ) (t : ℕ) (x : S) (u : A) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u)
  have hX : Measurable (fun ω : ℕ → ℝ × S × A => (s t ω, a t ω)) := (Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.snd h₁ t)
  let φ : S × A → ℝ := fun p => if p.1 = x ∧ p.2 = u then (1:ℝ) else 0
  have hF : ∀ k, Integrable (fun ω => (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
      (γ ^ k * r (t + k) ω)) (M θ) := fun k =>
    ((Integrable_Mul_R.of.Measurable h₁ (M := M) _ hX θ φ (t + k)).const_mul (γ ^ k)).congr
      (ae_of_all _ fun ω => by simp only [φ]; ring)
  have hN : ∀ k, ∫ ω, ‖(if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * (γ ^ k * r (t + k) ω)‖
    ∂(M θ) ≤ γ ^ k * |M.env.R| := by
    intro k
    have hb : ∀ᵐ ω ∂(M θ), ‖‖(if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
        (γ ^ k * r (t + k) ω)‖‖ ≤ γ ^ k * |M.env.R| := by
      filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint h₁ (M := M) θ] with ω h
      rw [norm_norm, norm_mul, norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact (mul_le_of_le_one_left (mul_nonneg (pow_nonneg h₀.1 k) (norm_nonneg _))
        (by split_ifs <;> simp)).trans (mul_le_mul_of_nonneg_left (h (t + k)) (pow_nonneg h₀.1 k))
    have := norm_integral_le_of_norm_le_const hb
    simp only [probReal_univ, mul_one] at this
    exact (Real.le_norm_self _).trans this
  have hS : Summable (fun k => ∫ ω, ‖(if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
      (γ ^ k * r (t + k) ω)‖ ∂(M θ)) :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun ω => norm_nonneg _) hN
      ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right _)
  have e : ∀ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω =
      ∑' k, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * (γ ^ k * r (t + k) ω) := fun ω => by
    dsimp only [Dot.dot, Function.getSliceFrom]
    simp only [Function.hPow_apply, id_eq]
    rw [← tsum_mul_left]
  refine (integral_congr_ae (Filter.Eventually.of_forall e)).trans ?_
  rw [← (hasSum_integral_of_summable_integral_norm hF hS).tsum_eq]
  have e2 : ∀ k, ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * (γ ^ k * r (t + k) ω) ∂(M θ) =
      ((M θ).real (s t ⁻¹' {x}) * M.policy.prob θ x u) *
        (γ ^ k * ∫ ω, r (t + k) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}]) := fun k => by
    have e_mul : (fun ω => (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * (γ ^ k * r (t + k) ω)) =
        fun ω => γ ^ k * ((if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * r (t + k) ω) :=
      funext fun ω => by ring
    rw [e_mul, integral_const_mul, E_ind_r h₁]
    ring
  simp_rw [e2]
  rw [tsum_mul_left]
  have hpR : Measurable (fun ω t ↦ r t ω) := Measurable.of_eval (Random.Measurable.of.All_Eq.fst h₁)
  have hfG : Measurable (fun integ : ℕ → ℝ ↦ (γ ^ (id : ℕ → ℕ)) @ integ[t:]) :=
    Measurable.tsum fun k => (measurable_pi_apply (t + k)).const_mul _
  have hpre : (s t, a t) ⁻¹' {(x, u)} = s t ⁻¹' {x} ∩ a t ⁻¹' {u} := by
    ext ω
    simp [JointRandomSymbol]
  have hQ : Q θ t x u =
      ∑' k, γ ^ k * ∫ ω, r (t + k) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] := by
    simp only [Q, Expectation.asRV_process]
    rw [Expectation.condEvent_eq_integral hpR.aemeasurable hfG, hpre]
    show ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω ∂(M θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] = _
    exact Integral_G.eq.TSum_MulPowIntegral_R_Add.of.In_Ico (M := M) h₀ h₁ θ _ t
  show _ = _ * Q θ t x u
  rw [hQ]


-- created on 2026-10-10
