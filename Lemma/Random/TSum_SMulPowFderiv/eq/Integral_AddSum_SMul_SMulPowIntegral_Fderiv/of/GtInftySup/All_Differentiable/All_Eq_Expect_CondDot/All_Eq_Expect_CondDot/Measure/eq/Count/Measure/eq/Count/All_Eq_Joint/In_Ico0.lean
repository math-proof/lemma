import Lemma.Random.Zero.eq.AddSum_SMulPowSum_SMul_SMulPow_Sum_SMul.of.Real.ne.Zero.GtInftySup.All_Differentiable.All_Eq_Expect_CondDot.All_Eq_Expect_CondDot.Measure.eq.Count.Measure.eq.Count.All_Eq_Joint.In_Ico0
import sympy.stats.cond_expectation
import sympy.core.power
import sympy.vector.Basic
import sympy.vector.operators
import Mathlib.Analysis.Calculus.Gradient.Basic
import sympy.concrete.sup
import Lemma.Random.RealPreimageSPreimageS_Add.eq.Pn.of.Ne0Real_Preimage
import Lemma.Random.RealPreimageS0.eq.Real
import Lemma.Random.RealPreimageS.eq.Sum_MulRealPn
import Lemma.Random.Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Integral.eq.Sum_SMul
import Lemma.Random.Integral_SMul.eq.Sum_SMul.of.All_Differentiable_Prob
import Lemma.Random.TSum_SMul.eq.Sum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob
import Lemma.Random.Integrable_Fun
import Lemma.Random.Measurable.Measurable.Measurable.of.All_Eq
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Finite-horizon policy gradient: for every `n`,
`γ ** Stack[t](t) @ ∇𝔼[r] = 𝔼[∑ t < n, γ ^ t * Q(s[t], a[t]) • ∇ log π(a[t] | s[t])] + γ ^ n • 𝔼[∇V(s[n])]`,
where `γ ** Stack[t](t) @ ∇𝔼[r]` is `∑' t, γ ^ t • ∇_θ 𝔼[r[t]]`.
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
  (h₅ : sup[θ, x, u] ‖∇[θ] M.pol.prob θ x u‖ < ∞)
  (n : ℕ) :
-- imply
  ∑' t, γ ^ t • fderiv ℝ (fun θ => ∫ ω, r t ω ∂(M θ)) θ =
    ∫ ω, ∑ t ∈ Finset.range n, (γ ^ t * Q θ t (s t ω) (a t ω)) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ) +
      γ ^ n • ∫ ω, fderiv ℝ (fun θ' => V θ' n (s n ω)) θ ∂(M θ) := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  have h₄n := h₅
  simp only [gradient, LinearIsometryEquiv.norm_map] at h₅
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
  have h₇ : ∀ θ x u, ‖fderiv ℝ (fun θ => M.pol.prob θ x u) θ‖ ≤ C := fun θ x u => hC ⟨(θ, x, u), rfl⟩
  classical
  have hQ_expect : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A),
      Qloc θ t («s.bvar» t) («a.bvar» t) =
        𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t) :=
    fun _ _ _ _ => rfl
  have hV_expect : ∀ θ t («s.bvar» : ℕ → S),
      Vloc θ t («s.bvar» t) =
        𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t) :=
    fun _ _ _ => rfl
  have h₈ : ∀ x, M.env.init.real {x} • fderiv ℝ (fun θ => M.Vc θ γ x) θ =
      M.env.init.real {x} • (∑ t ∈ Finset.range n, γ ^ t • ∑ y, M.Pn θ t x y •
          ∑ u, Qloc θ t y u • fderiv ℝ (fun θ => M.pol.prob θ y u) θ +
        γ ^ n • ∑ y, M.Pn θ n x y • fderiv ℝ (fun θ => Vloc θ n y) θ) := by
    intro x
    if hx : M.env.init.real {x} = 0 then
      rw [hx, zero_smul, zero_smul]
    else
      have hP : (M θ).real (s 0 ⁻¹' {x}) ≠ 0 := by rwa [RealPreimageS0.eq.Real h₁]
      have hg := Zero.eq.AddSum_SMulPowSum_SMul_SMulPow_Sum_SMul.of.Real.ne.Zero.GtInftySup.All_Differentiable.All_Eq_Expect_CondDot.All_Eq_Expect_CondDot.Measure.eq.Count.Measure.eq.Count.All_Eq_Joint.In_Ico0 (Q := Qloc) (V := Vloc) h₀ h₁ hS hA hQ_expect hV_expect h₄ h₄n hP n
      have h' : ∀ t y, ((M θ)[|s 0 ⁻¹' {x}]).real (s t ⁻¹' {y}) = M.Pn θ t x y := fun t y => by
        have h'' := RealPreimageSPreimageS_Add.eq.Pn.of.Ne0Real_Preimage (M := M) θ 0 t x y h₁ hP
        rwa [zero_add] at h''
      simp_rw [h'] at hg
      have h : fderiv ℝ (fun θ => Vloc θ 0 x) θ =
          ∑ t ∈ Finset.range n, γ ^ t • ∑ y, M.Pn θ t x y •
              ∑ u, Qloc θ t y u • fderiv ℝ (fun θ => M.pol.prob θ y u) θ +
            γ ^ n • ∑ y, M.Pn θ n x y • fderiv ℝ (fun θ => Vloc θ n y) θ := by
        apply (InnerProductSpace.toDual ℝ Θ).symm.injective
        simpa [gradient, map_add, map_smul, map_sum] using hg
      rw [← Fderiv_V.eq.Fderiv_Vc.of.Ne0Real_Preimage.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) 0 x θ h₀ h₁ h₄ h₄n hP, h]
  have h₉ : ∀ t, ∫ ω, (γ ^ t * Qloc θ t (s t ω) (a t ω)) •
      fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' (s t ω) (a t ω))) θ ∂(M θ) =
      ∑ y, (M θ).real (s t ⁻¹' {y}) •
        ∑ u, (γ ^ t * Qloc θ t y u) • fderiv ℝ (fun θ' => M.pol.prob θ' y u) θ :=
    fun t => Integral_SMul.eq.Sum_SMul.of.All_Differentiable_Prob (M := M) h₁ h₄ θ t (fun y u => γ ^ t * Qloc θ t y u)
  have h₁₀ : ∫ ω, fderiv ℝ (fun θ' => Vloc θ' n (s n ω)) θ ∂(M θ) =
      ∑ y, (M θ).real (s n ⁻¹' {y}) • fderiv ℝ (fun θ' => Vloc θ' n y) θ :=
    Integral.eq.Sum_SMul h₁ (M := M) θ n (fun y => fderiv ℝ (fun θ' => Vloc θ' n y) θ)
  rw [TSum_SMul.eq.Sum_SMul.of.In_Ico.GtInftySup.All_Differentiable_Prob (M := M) h₀ h₁ h₄ h₄n θ, Finset.sum_congr rfl fun x _ => h₈ x,
    integral_finsetSum _ fun t _ => Random.Integrable_Fun h₁ (M := M) θ t
      (fun y u => (γ ^ t * Qloc θ t y u) • fderiv ℝ (fun θ' => Real.log (M.pol.prob θ' y u)) θ)]
  simp_rw [h₉, h₁₀, RealPreimageS.eq.Sum_MulRealPn (M := M) h₁ θ]
  simp only [smul_add, Finset.sum_add_distrib, Finset.smul_sum, Finset.sum_smul, smul_smul,
    Finset.sum_mul]
  congr 1
  ·
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun x _ => ?_
    congr 1
    ring
  ·
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
    congr 1
    ring


-- created on 2023-04-04
