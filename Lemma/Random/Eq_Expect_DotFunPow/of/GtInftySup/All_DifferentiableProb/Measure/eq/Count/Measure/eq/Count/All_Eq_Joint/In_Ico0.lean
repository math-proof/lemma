import Lemma.Random.TSum_SMulPowFderiv.eq.TSum_SMulPow_Integral_SMul.of.GtInftySup.All_Differentiable.All_Eq_Expect_CondDot.All_Eq_Expect_CondDot.Measure.eq.Count.Measure.eq.Count.All_Eq_Joint.In_Ico0
import Lemma.Random.Integral_SMulGetDotFderivLog.eq.Integral_SMulQFderiv.of.All_Eq_Joint.InIco0
import Lemma.Random.Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.Measure.eq.Count.Measure.eq.Count.All_Eq_Joint.In_Ico0
import Lemma.Random.ProbCond.eq.OfRealPol.of.Ne_0
import Lemma.Random.SinglePSpace.of.EqMeasureCount.Measurable
import Lemma.Measure.Count.eq.ProdCountS
import Lemma.Measure.EqRnDeriv_Count
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import sympy.stats.variance
import sympy.vector.Basic
import sympy.vector.operators
import sympy.concrete.sup
import sympy.stats.cond_expectation
import sympy.core.power
import Lemma.Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob
import Lemma.Random.GetTSum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.AeRealPreimageSS.ne.Zero
import Lemma.Random.BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Measure
open scoped ENNReal.ToRealCoe


/--
Policy-gradient theorem (REINFORCE form), with the discounted return `γ ** Stack[t](t) @ r`:
`∇𝔼[γ ** Stack[t](t) @ r] = 𝔼[∑' t, γ ^ t • (γ ** Stack[k](k) @ r[t:]) • ∇ log π(a[t] | s[t])]`.
`h₂`, `h₃`: `θ ↦ π_θ(u | x)` is differentiable with a uniformly bounded gradient
(without them the statement is false). The bound on `∇V` over the reachable pairs
`(t, x)` is not assumed: it follows from time-homogeneity and the finiteness of `S` (`Random.BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob`). Densities are taken w.r.t. the counting
measures (`hS`, `hA`), so `ℙ[M θ](a[t] = u | s[t] = x)` is the policy `π_θ(u | x)` at reachable states.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [ReferenceMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [ReferenceMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hS : (ReferenceMeasure.measure : Measure S) = Measure.count)
  (hA : (ReferenceMeasure.measure : Measure A) = Measure.count)
  (h₂ : ∀ x u, Differentiable ℝ (fun θ => M.pol.prob θ x u))
  (h₃ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    SinglePSpace.of.EqMeasureCount.Measurable ((Random.Measurable.of.All_Eq.snd.snd h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.fst h₁ t)) (by
      show (ReferenceMeasure.measure : Measure A).prod (ReferenceMeasure.measure : Measure S) = _
      rw [hA, hS, Count.eq.ProdCountS])
  have hs : ∀ t, PSpace (M θ) (s t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.snd.fst h₁ t).aemeasurable⟩
  have ha : ∀ t, PSpace (M θ) (a t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.snd.snd h₁ t).aemeasurable⟩
  have hr : ∀ t, PSpace (M θ) (r t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩
  have : PSpace (M θ) (AsPathRV.path (s)) :=
    PSpace.of_process_path hs
  have : PSpace (M θ) (AsPathRV.path (a)) :=
    PSpace.of_process_path ha
  have : PSpace (M θ) (AsPathRV.path (r)) :=
    PSpace.of_process_path hr
  let : MeasurableSpace Θ := borel Θ
  have : BorelSpace Θ := ⟨rfl⟩
  ∇[θ] (
    have : PSpace (M θ) (AsPathRV.path (r)) :=
      PSpace.of_process_path (fun t => ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩)
    𝔼[r: M θ](((fun t : ℕ => γ ^ t) @ r))) =
    -- TODO(sympy 𝔼 patch): 𝔽((a₀ t) = … | (s₀ t) = …) with let a₀ := a; let s₀ := s
    let a₀ := a
    let s₀ := s
    𝔼[s, a, r : M θ](
      ∑' t, γ ^ t •
        (((fun k : ℕ => γ ^ k) @ (fun k : ℕ => r (t + k))) •
          ∇[θ] (ℙ[M θ]((a₀ t) = (a t) | (s₀ t) = (s t)) : ℝ).log)) := by
-- proof
  intro hP _ _ _ _ _ _
  classical
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  let _ : MeasurableSpace Θ := borel Θ
  have _ : BorelSpace Θ := ⟨rfl⟩
  have h₃o := h₃
  simp only [gradient, LinearIsometryEquiv.norm_map] at h₃
  have hfd : ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
      ∑' t, γ ^ t • ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
    obtain ⟨C, hC⟩ := id h₃
    have hCb : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ C := fun θ x u => hC ⟨(θ, x, u), rfl⟩
    classical
    let Qloc (θ : Θ) (t : ℕ) (x : S) (u : A) : ℝ :=
      𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u)
    have hQ_expect : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A),
        Qloc θ t («s.bvar» t) («a.bvar» t) =
          𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t) :=
      fun _ _ _ _ => rfl
    let Vloc (θ : Θ) (t : ℕ) (x : S) : ℝ :=
      𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x)
    have hV_expect : ∀ θ t («s.bvar» : ℕ → S),
        Vloc θ t («s.bvar» t) =
          𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t) :=
      fun _ _ _ => rfl
    rw [TSum_SMulPowFderiv.eq.TSum_SMulPow_Integral_SMul.of.GtInftySup.All_Differentiable.All_Eq_Expect_CondDot.All_Eq_Expect_CondDot.Measure.eq.Count.Measure.eq.Count.All_Eq_Joint.In_Ico0 (Q := Qloc) (V := Vloc) h₀ h₁ hS hA hQ_expect hV_expect h₂ h₃o]
    refine tsum_congr fun t => congrArg (fun z => γ ^ t • z) ?_
    exact (Integral_SMulGetDotFderivLog.eq.Integral_SMulQFderiv.of.All_Eq_Joint.InIco0 (M := M) (θ := θ) h₀ h₁).symm
  have hscore : ∀ t, ∀ᵐ ω ∂(M θ),
      fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ =
        fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ := by
    intro t
    filter_upwards [AeRealPreimageSS.ne.Zero (s := s) (M := M) θ] with ω hω
    have hc : ContinuousAt (fun θ' => (M θ').real (s t ⁻¹' {s t ω})) θ :=
      (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₂ h₃o t (s t ω) θ).continuousAt
    refine Filter.EventuallyEq.fderiv_eq ((hc.eventually_ne (hω t)).mono fun θ' h => ?_)
    beta_reduce
    rw [ProbCond.eq.OfRealPol.of.Ne_0 h₁ hS hA (hP θ' t) h,
      ENNReal.toReal_ofReal (M.pol.nonneg θ' _ _)]
  have hold : ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
      ∑' t, γ ^ t • ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω •
          fderiv ℝ (fun θ' => (ℙ[M θ']((a t) = (a t ω) | (s t) = (s t ω)) : ℝ).log) θ ∂(M θ) := by
    rw [hfd]
    refine tsum_congr fun t => ?_
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hscore t] with ω hω
    rw [hω]
  let L : StrongDual ℝ Θ ≃L[ℝ] Θ := (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv
  have hL : ∀ φ, (InnerProductSpace.toDual ℝ Θ).symm φ = L φ := fun _ => rfl
  -- almost sure bound of the discounted return from `t`
  have hA' : ∀ᵐ ω ∂(M θ), ∀ t, ‖∑' k, γ ^ k * r (t + k) ω‖ ≤ (1 - γ)⁻¹ * |M.env.R| := by
    filter_upwards [All_LeNorm_Abs.of.All_Eq_Joint h₁ (M := M) θ] with ω hr t
    refine tsum_of_norm_bounded ((hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right _) fun k => ?_
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
    exact mul_le_mul_of_nonneg_left (hr _) (pow_nonneg h₀.1 k)
  -- the reward series
  have hRint : ∀ θ' : Θ, ∫ ω, ∑' t, γ ^ t * r t ω ∂(M θ') = ∑' t, γ ^ t * ∫ ω, r t ω ∂(M θ') := by
    intro θ'
    have hrb : ∀ t, ∀ᵐ ω ∂(M θ'), ‖γ ^ t * r t ω‖ ≤ γ ^ t * |M.env.R| := fun t =>
      (All_LeNorm_Abs.of.All_Eq_Joint h₁ (M := M) θ').mono fun ω h => by
        rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1]
        exact mul_le_mul_of_nonneg_left (h t) (pow_nonneg h₀.1 t)
    have hri : ∀ t, Integrable (fun ω => γ ^ t * r t ω) (M θ') := fun t =>
      Integrable.of_bound ((Random.Measurable.of.All_Eq.fst h₁ t).const_mul (γ ^ t)).aestronglyMeasurable _ (hrb t)
    rw [← integral_tsum_of_summable_integral_norm hri]
    · exact tsum_congr fun t => integral_const_mul _ _
    ·
      refine Summable.of_nonneg_of_le (fun t => integral_nonneg fun _ => norm_nonneg _) (fun t => ?_)
        ((summable_geometric_of_lt_one h₀.1 h₀.2).mul_right |M.env.R|)
      calc
        _ ≤ ∫ _, γ ^ t * |M.env.R| ∂(M θ') :=
          integral_mono_ae (hri t).norm (integrable_const _) (hrb t)
        _ = γ ^ t * |M.env.R| := by simp
  have hRb := Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.Measure.eq.Count.Measure.eq.Count.All_Eq_Joint.In_Ico0 (X := fun _ _ r k => r k)
    h₀ h₁ hS hA (fun k => Random.Measurable.of.All_Eq.fst h₁ k) hA' h₂ h₃o
  refine Eq.trans ?_ ((congrArg L hold).trans hRb)
  rw [← (GetTSum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃o θ).fderiv, gradient, hL]
  congr 2
  funext θ'
  -- `𝔼[r: M θ']((fun t => γ ^ t) @ r)` is the Bochner integral of the return
  have hr' : ∀ t, PSpace (M θ') (r t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩
  have hpr' : PSpace (M θ') (AsPathRV.path (r)) :=
    PSpace.of_process_path hr'
  refine Eq.trans ?_ (hRint θ')
  simp only [Expectation.asRV_process, Dot.dot]
  rw [Expectation.ofRV, expectation_real]
  refine (integral_map hpr'.aemeasurable ?_).trans ?_
  · exact (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
      (measurable_pi_apply t).const_mul (γ ^ t)).aestronglyMeasurable
  · rfl


-- created on 2023-04-07
-- updated on 2026-10-10
