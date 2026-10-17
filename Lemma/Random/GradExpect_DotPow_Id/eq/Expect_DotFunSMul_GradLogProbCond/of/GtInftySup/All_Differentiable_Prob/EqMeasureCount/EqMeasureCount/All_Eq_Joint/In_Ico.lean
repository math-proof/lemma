import Lemma.Random.TSum_SMulPowFderiv.eq.Integral_AddSum_SMul_SMulPowIntegral_Fderiv.of.GtInftySup.All_Differentiable.All_Eq_Expect_CondDot.All_Eq_Expect_CondDot.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico0
import Lemma.Real.Eq_0.Lim.of.LtAbs.GtInftySup
import Lemma.Random.Integral.eq.Sum_SMul
import Lemma.Random.NormQ.le.MulSub1Abs_R.of.In_Ico
import Lemma.Random.Integral_SMul.eq.Sum_SMul.of.All_Differentiable_Prob
import Lemma.Random.Sum_RealPreimageS.eq.One
import Lemma.Random.Integrable_Fun
import Lemma.Random.BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Integral_SMulGetDotFderivLog.eq.Integral_SMulQFderiv.of.All_Eq_Joint.InIco0
import Lemma.Random.Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico0
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
import Lemma.Random.All_LeNorm_Abs.of.All_Eq_Joint
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
import Lemma.Random.PSpace_Path.of.All_PSpace
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Real Measure Set
open scoped ENNReal.ToRealCoe
set_option maxHeartbeats 40000000


/--
Policy-gradient theorem (REINFORCE form), with the discounted return `γ ** Stack[t](t) @ r`:
`∇𝔼[γ ** Stack[t](t) @ r] = 𝔼[(γ ^ (id : ℕ → ℕ)) @ (fun t ↦ (γ ** Stack[k](k) @ r[t:]) • ∇ log π(a[t] | s[t]))]`.
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
  have : PSpace (M θ) (AsPathRV.path (s)) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path (a)) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd h₁ t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path (r)) := fun θ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩)
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) @ r) = 𝔼[s, a, r : M θ]((γ ^ (id : ℕ → ℕ)) @ fun t ↦ ((γ ^ (id : ℕ → ℕ)) @ r[t:]) • ∇[θ] (ℙ[M θ](a t | s t) : ℝ).log) := by
-- proof
  intro hP _ _ _
  classical
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
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
    -- inlined from former In_Ico1 (fderiv/CLM Q-score series)
    have h7grad :=
      TSum_SMulPowFderiv.eq.Integral_AddSum_SMul_SMulPowIntegral_Fderiv.of.GtInftySup.All_Differentiable.All_Eq_Expect_CondDot.All_Eq_Expect_CondDot.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico0
        (θ := θ) h₀ h₁ hS hA hQ_expect hV_expect h₂ h₃o
    let Lgrad : StrongDual ℝ Θ ≃L[ℝ] Θ :=
      (InnerProductSpace.toDual ℝ Θ).symm.toContinuousLinearEquiv
    have hLgrad : ∀ φ, (InnerProductSpace.toDual ℝ Θ).symm φ = Lgrad φ := fun _ => rfl
    have hsumLgrad :
        Summable
          (fun t => γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ) := by
      have hs :=
        Summable_MulPowMulAdd_1.of.In_Ico h₀ (Fintype.card A * C * |M.env.R|)
      refine Summable.of_norm_bounded hs fun t => ?_
      rw [norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
      exact mul_le_mul_of_nonneg_left
        ((Differentiable.All_LeNormFderivMulAdd_1MulMulCardAbs_R.of.All_LeNormFderiv.All_Differentiable_Prob
            (M := M) h₁ h₂ hCb t).2 θ)
        (pow_nonneg h₀.1 t)
    have h₇ :
        ∀ n,
          ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
            ∫ ω,
                ∑ t ∈ Finset.range n,
                  (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
                    fderiv ℝ
                      (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω)))
                      θ ∂(M θ) +
              γ ^ n •
                ∫ ω, fderiv ℝ (fun θ' => Vloc θ' n (s n ω)) θ ∂(M θ) := by
      intro n
      have H := h7grad n
      simp only [Dot.dot, Function.hPow_apply, id_eq, gradient] at H
      simp_rw [hLgrad] at H
      have hInt :
          Integrable
            (fun ω ↦
              ∑ t ∈ Finset.range n,
                (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
                  fderiv ℝ
                    (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ)
            (M θ) :=
        integrable_finsetSum _ fun t _ =>
          Random.Integrable_Fun h₁ (M := M) θ t
            (fun y u =>
              (γ ^ t * Qloc θ t y u) •
                fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ)
      have hIntV :
          Integrable
            (fun ω ↦ fderiv ℝ (fun θ' => Vloc θ' n (s n ω)) θ) (M θ) :=
        Random.Integrable_Fun h₁ (M := M) θ n
          (fun y _ => fderiv ℝ (fun θ' => Vloc θ' n y) θ)
      apply Lgrad.injective
      have := hsumLgrad
      have := hInt
      have := hIntV
      refine Eq.trans Lgrad.map_tsum ?_
      refine Eq.trans (tsum_congr fun t => map_smul Lgrad (γ ^ t) _) ?_
      refine H.trans ?_
      refine Eq.trans ?_ (map_add Lgrad _ _).symm
      congr 1
      ·
        refine Eq.trans ?_ (Lgrad.integral_comp_comm _)
        congr 1
        refine funext fun ω =>
          Eq.trans (Finset.sum_congr rfl fun t _ => (map_smul Lgrad _ _).symm)
            (_root_.map_sum Lgrad _ _).symm
      ·
        refine Eq.trans (congrArg (fun z => γ ^ n • z) (Lgrad.integral_comp_comm _)) ?_
        exact (map_smul Lgrad (γ ^ n) _).symm
    obtain ⟨B, hB⟩ :=
      BddAbove_ImageNormFderiv.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃o θ
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
    have h₁₀ :
        Tendsto (fun n => γ ^ n * ‖∫ ω, fderiv ℝ (fun θ' => Vloc θ' n (s n ω)) θ ∂(M θ)‖) atTop (𝓝 0) :=
      Eq_0.Lim.of.LtAbs.GtInftySup hγ
        ⟨max B 0, by rintro _ ⟨n, rfl⟩; exact (abs_norm _).trans_le (h₉ n)⟩
    have h₁₁ :
        Tendsto (fun n => γ ^ n • ∫ ω, fderiv ℝ (fun θ' => Vloc θ' n (s n ω)) θ ∂(M θ)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine h₁₀.congr fun n => ?_
      rw [norm_smul, norm_pow, Real.norm_of_nonneg h₀.1]
    have hq : 0 ≤ (1 - γ)⁻¹ * |M.env.R| := mul_nonneg (inv_nonneg.2 (by linarith [h₀.2])) (abs_nonneg _)
    have h₁₂ : ∀ t, ‖∫ ω, Qloc θ t (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ)‖ ≤
        Fintype.card A * ((1 - γ)⁻¹ * |M.env.R| * max C 0) := by
      intro t
      rw [Integral_SMul.eq.Sum_SMul.of.All_Differentiable_Prob (M := M) h₁ h₂ θ t (fun y u => Qloc θ t y u)]
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
              ((hCb θ y u).trans (le_max_left _ _)) (norm_nonneg _) hq
          ·
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = _ := by rw [← Finset.sum_mul, Sum_RealPreimageS.eq.One h₁, one_mul]
    have h₁₃ : Summable (fun t => γ ^ t • ∫ ω, Qloc θ t (s t ω) (a t ω) •
        fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ)) := by
      have hs := (summable_geometric_of_lt_one h₀.1 h₀.2).mul_right
        (Fintype.card A * ((1 - γ)⁻¹ * |M.env.R| * max C 0))
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
    have hQseries :
        ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
          ∑' t, γ ^ t • ∫ ω, Qloc θ t (s t ω) (a t ω) •
            fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ) := by
      refine tendsto_nhds_unique (tendsto_const_nhds.congr fun n => ?_) h₁₅
      rw [h₇ n, h₁₄ n]
    rw [hQseries]
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
  have hRb := Eq_SymmToDualTSum_SMulPow_Integral_SMulTSum_MulPow_FderivLogToRealProbCond.of.GtInftySup.All_Differentiable.AeAll_LeNormTSum_MulPow.All_Measurable.EqMeasureCount.EqMeasureCount.All_Eq_Joint.In_Ico0 (X := fun _ _ r k => r k)
    h₀ h₁ hS hA (fun k => Random.Measurable.of.All_Eq.fst h₁ k) hA' h₂ h₃o
  refine Eq.trans ?_ ((congrArg L hold).trans hRb)
  rw [← (GetTSum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₂ h₃o θ).fderiv, gradient, hL]
  congr 2
  funext θ'
  have hr' : ∀ t, PSpace (M θ') (r t) := fun t =>
    ⟨(Random.Measurable.of.All_Eq.fst h₁ t).aemeasurable⟩
  have hpr' : PSpace (M θ') (AsPathRV.path (r)) :=
    PSpace_Path.of.All_PSpace hr'
  refine Eq.trans ?_ (hRint θ')
  simp only [Expectation.asRV_process, Dot.dot]
  rw [Expectation.ofRV, expectation_real]
  refine (integral_map hpr'.aemeasurable ?_).trans ?_
  · exact (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
      (measurable_pi_apply t).const_mul (γ ^ t)).aestronglyMeasurable
  · rfl


-- created on 2023-04-07
-- updated on 2026-10-17
