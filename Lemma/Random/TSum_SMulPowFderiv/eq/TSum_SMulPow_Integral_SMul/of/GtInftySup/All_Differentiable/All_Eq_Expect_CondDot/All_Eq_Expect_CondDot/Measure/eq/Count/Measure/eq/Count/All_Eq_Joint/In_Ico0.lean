import Lemma.Random.TSum_SMulPowFderiv.eq.Integral_AddSum_SMul_SMulPowIntegral_Fderiv.of.GtInftySup.All_Differentiable.All_Eq_Expect_CondDot.All_Eq_Expect_CondDot.Measure.eq.Count.Measure.eq.Count.All_Eq_Joint.In_Ico0
import Lemma.Real.Eq_0.Lim.of.LtAbs.GtInftySup
import sympy.stats.cond_expectation
import sympy.core.power
import sympy.vector.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import sympy.vector.operators
import sympy.concrete.sup
import Lemma.Random.Integral.eq.Sum_SMul
import Lemma.Random.NormQ.le.MulSub1Abs_R.of.In_Ico
import Lemma.Random.Integral_SMul.eq.Sum_SMul.of.All_Differentiable_Prob
import Lemma.Random.Sum_RealPreimageS.eq.One
import Lemma.Random.Integrable_Fun
import Lemma.Random.BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Real


/--
Policy-gradient theorem with action values:
`γ ** Stack[t](t) @ ∇𝔼[r] = ∑' t, γ ^ t • 𝔼[Q(s[t], a[t]) • ∇ log π(a[t] | s[t])]`,
the limit `n → ∞` of `policy_gradient`: `γ ^ n • 𝔼[∇V(s[n])] → 0`, because `∇V(s[t])` is bounded over
the reachable pairs `Pr(s[t] = x) ≠ 0` (`BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob`: time-homogeneity and the finiteness of `S`).
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {Q : Θ → ℕ → S → A → ℝ}
  {V : Θ → ℕ → S → ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hS : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (hA : (ReferenceMeasure.measure : Measure A) = Measure.count)
  (h₂ : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A), Q θ t («s.bvar» t) («a.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t))
  (h₃ : ∀ θ t («s.bvar» : ℕ → S), V θ t («s.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t))
  (h₄ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₅ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞) :
-- imply
  ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
    ∑' t, γ ^ t • ∫ ω, Q θ t (s t ω) (a t ω) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  have h₄n := h₅
  simp only [gradient, LinearIsometryEquiv.norm_map] at h₅
  have h₇ := TSum_SMulPowFderiv.eq.Integral_AddSum_SMul_SMulPowIntegral_Fderiv.of.GtInftySup.All_Differentiable.All_Eq_Expect_CondDot.All_Eq_Expect_CondDot.Measure.eq.Count.Measure.eq.Count.All_Eq_Joint.In_Ico0 (θ := θ) h₀ h₁ hS hA h₂ h₃ h₄ h₄n
  let Qloc (θ : Θ) (t : ℕ) (x : S) (u : A) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u)
  let Vloc (θ : Θ) (t : ℕ) (x : S) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x)
  have hQ : Q = Qloc := funext fun θ => funext fun t => funext fun x => funext fun u =>
    h₂ θ t (fun _ ↦ x) (fun _ ↦ u)
  have hV : V = Vloc := funext fun θ => funext fun t => funext fun x =>
    h₃ θ t (fun _ ↦ x)
  subst hQ hV
  obtain ⟨C, hC⟩ := id h₅
  have h₈ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ C := fun θ x u => hC ⟨(θ, x, u), rfl⟩
  classical
  beta_reduce at h₇ ⊢
  obtain ⟨B, hB⟩ := BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₄ h₄n θ
  have h₉ : ∀ n, ‖∫ ω, fderiv ℝ (fun θ' => Vloc θ' n (s n ω)) θ ∂(M θ)‖ ≤ max B 0 := by
    intro n
    rw [Integral.eq.Sum_SMul h₁ (M := M) θ n (fun y => fderiv ℝ (fun θ' => Vloc θ' n y) θ)]
    calc
      _ ≤ ∑ y, ‖(M θ).real (s n ⁻¹' {y}) • fderiv ℝ (fun θ' => Vloc θ' n y) θ‖ :=
        norm_sum_le _ _
      _ ≤ ∑ y, (M θ).real (s n ⁻¹' {y}) * max B 0 := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [norm_smul, Real.norm_of_nonneg measureReal_nonneg]
        if hy : (M θ).real (s n ⁻¹' {y}) = 0 then
          rw [hy, zero_mul, zero_mul]
        else
          exact mul_le_mul_of_nonneg_left ((hB ⟨(n, y), hy, rfl⟩).trans (le_max_left _ _)) measureReal_nonneg
      _ = max B 0 := by rw [← Finset.sum_mul, Sum_RealPreimageS.eq.One h₁, one_mul]
  have hγ : |γ| < 1 := by
    rw [abs_of_nonneg h₀.1]
    apply h₀.2
  have h₁₀ : Tendsto (fun n => γ ^ n * ‖∫ ω, fderiv ℝ (fun θ' => Vloc θ' n (s n ω)) θ ∂(M θ)‖) atTop (𝓝 0) :=
    Eq_0.Lim.of.LtAbs.GtInftySup hγ
      ⟨max B 0, by rintro _ ⟨n, rfl⟩; exact (abs_norm _).trans_le (h₉ n)⟩
  have h₁₁ : Tendsto (fun n => γ ^ n • ∫ ω, fderiv ℝ (fun θ' => Vloc θ' n (s n ω)) θ ∂(M θ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine h₁₀.congr fun n => ?_
    rw [norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
  have hq : 0 ≤ (1 - γ)⁻¹ * |M.env.R| := mul_nonneg (inv_nonneg.2 (by linarith [h₀.2])) (abs_nonneg _)
  have h₁₂ : ∀ t, ‖∫ ω, Qloc θ t (s t ω) (a t ω) •
      fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ)‖ ≤
      Fintype.card A * ((1 - γ)⁻¹ * |M.env.R| * max C 0) := by
    intro t
    rw [Integral_SMul.eq.Sum_SMul.of.All_Differentiable_Prob (M := M) h₁ h₄ θ t (fun y u => Qloc θ t y u)]
    calc
      _ ≤ ∑ y, ‖(M θ).real (s t ⁻¹' {y}) •
          ∑ u, Qloc θ t y u • fderiv ℝ (fun θ' => M.pol.prob θ' y u) θ‖ :=
        norm_sum_le _ _
      _ ≤ ∑ y, (M θ).real (s t ⁻¹' {y}) * (Fintype.card A * ((1 - γ)⁻¹ * |M.env.R| * max C 0)) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [norm_smul, Real.norm_of_nonneg measureReal_nonneg]
        refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_sum (g := fun _ => (1 - γ)⁻¹ * |M.env.R| * max C 0) fun u _ => ?_).trans_eq ?_
        ·
          rw [norm_smul]
          exact mul_le_mul (NormQ.le.MulSub1Abs_R.of.In_Ico (M := M) h₀ h₁ θ t y u)
            ((h₈ θ y u).trans (le_max_left _ _)) (norm_nonneg _) hq
        ·
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = _ := by rw [← Finset.sum_mul, Sum_RealPreimageS.eq.One h₁, one_mul]
  have h₁₃ : Summable (fun t => γ ^ t • ∫ ω, Qloc θ t (s t ω) (a t ω) •
      fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ)) := by
    have hs := (summable_geometric_of_lt_one h₀.1 h₀.2).mul_right (Fintype.card A * ((1 - γ)⁻¹ * |M.env.R| * max C 0))
    refine Summable.of_norm_bounded hs fun t => ?_
    rw [norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
    exact mul_le_mul_of_nonneg_left (h₁₂ t) (pow_nonneg h₀.1 t)
  have h₁₄ : ∀ n, ∫ ω, ∑ t ∈ Finset.range n, (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
      fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ) =
      ∑ t ∈ Finset.range n, γ ^ t • ∫ ω, Qloc θ t (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
    intro n
    rw [integral_finsetSum _ fun t _ => Random.Integrable_Fun h₁ (M := M) θ t
      (fun y u => (γ ^ t * Qloc θ t y u) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ)]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp_rw [mul_smul]
    exact integral_smul _ _
  have h₁₅ := h₁₃.hasSum.tendsto_sum_nat.add h₁₁
  rw [add_zero] at h₁₅
  refine tendsto_nhds_unique (tendsto_const_nhds.congr fun n => ?_) h₁₅
  rw [h₇ n, h₁₄ n]


-- created on 2026-10-11
