import Lemma.Random.OfRV.eq.Integral.of.AEStronglyMeasurable_Map
import Lemma.Random.ProbCond.eq.OfRealPol.of.Ne_0
import Lemma.Random.ProbCond.eq.Div.of.SinglePSpace
import Lemma.Random.Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob
import Lemma.Random.AeRealPreimageSS.ne.Zero
import Lemma.Random.PSpace_Path.of.All_PSpace
import Lemma.Random.SinglePSpace.of.Measurable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
open scoped ENNReal.ToRealCoe
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Measure Set
open IsPolicyTrajectory
set_option maxHeartbeats 625000


/--
| attributes | lemma |
| :---: | :---: |
| path | Random.ExpectDot.eq.Integral_Dot_FunSMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.Ae_GtInftySup.All_Measurable.All_NeProb_0.IsPolicyTrajectory.In_Ico |
| comm | Random.Integral_Dot_FunSMul_GradLogProbCond.eq.ExpectDot.of.GtInftySup.All_Differentiable_Prob.Ae_GtInftySup.All_Measurable.All_NeProb_0.IsPolicyTrajectory.In_Ico |
-/
@[path, comm]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {X : (ℕ → ℝ) → (ℕ → S) → (ℕ → A) → ℕ → ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : IsPolicyTrajectory M r s a)
  (h₂ : ∀ θ («s.bvar» : ℕ ⇀ S) («a.bvar» : ℕ ⇀ A),
    ℙ[M θ](a[0] = «a.bvar»[0] ∧ s[0] = «s.bvar»[0]) ≠ 0)
  (h₃ : ∀ k, Measurable fun ω : ℕ → ℝ × S × A =>
    X (r · ω) (s · ω) (a · ω) k)
  (h₄ : ∀ᵐ ω ∂(M θ),
    sup[t] |((γ ^ (id : ℕ → ℕ)) @ (X (r · ω) (s · ω) (a · ω))[t:])| < ∞)
  (h₅ : ∀ t («s.bvar» : ℕ ⇀ S) («a.bvar» : ℕ ⇀ A),
    Differentiable ℝ (fun θ => (ℙ[M θ](a[t] = «a.bvar»[t] | s[t] = «s.bvar»[t]) : ℝ)))
  (h₆ : sup[θ, t, «s.bvar» : ℕ ⇀ S, «a.bvar» : ℕ ⇀ A]
    ‖∇[θ] (ℙ[M θ](a[t] = «a.bvar»[t] | s[t] = «s.bvar»[t]) : ℝ)‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
    SinglePSpace.of.Measurable ((Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁.stage_eq t).prodMk (Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁.stage_eq t))
  have : ∀ θ t, SinglePSpace (M θ) (s t) := fun _ t =>
    SinglePSpace.of.Measurable (Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁.stage_eq t)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace fun t =>
      ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁.stage_eq t).aemeasurable⟩
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace fun t =>
      ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁.stage_eq t).aemeasurable⟩
  have : PSpace (M θ) (AsPathRV.path r) :=
    PSpace_Path.of.All_PSpace fun t =>
      ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁.stage_eq t).aemeasurable⟩
  let : MeasurableSpace Θ := borel Θ
  have : BorelSpace Θ := ⟨rfl⟩
  𝔼[r, s, a : M θ](
    (γ ^ (id : ℕ → ℕ)) @ fun t ↦
      (((γ ^ (id : ℕ → ℕ)) @ (X r s a)[t:]) •
        ∇[θ] Real.log (ℙ[M θ](a[t] | s[t])).toReal)) =
  ∫ ω,
    ((γ ^ (id : ℕ → ℕ)) @ fun t ↦
      ((γ ^ (id : ℕ → ℕ)) @ (X (r · ω) (s · ω) (a · ω))[t:]) •
        ∇[θ] Real.log (ℙ[M θ](a[t] = (a t ω) | s[t] = (s t ω))).toReal) ∂(M θ) := by
-- proof
  intro hP _ _ _ _
  have h₁pol := h₁
  have : IsPolicyTrajectory M r s a := h₁
  classical
  obtain ⟨r⟩ := r
  obtain ⟨s⟩ := s
  obtain ⟨a⟩ := a
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁.stage_eq t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁.stage_eq t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁.stage_eq t) ω)).symm
  have h₁ := h₁pol.stage_eq
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  let _ : MeasurableSpace Θ := borel Θ
  have _ : BorelSpace Θ := ⟨rfl⟩
  -- h₀/h₂/h₄/h₅/h₆ unused after Expect=∫ (kept on statement for of-atoms / callers)
  have _ := h₀
  have _ := h₂
  have _ := h₄
  have _ := h₅
  have _ := h₆
  let fromPath := fun (p : (ℕ → ℝ) × (ℕ → S) × (ℕ → A)) =>
    fun t => (p.1 t, p.2.1 t, p.2.2 t)
  have fromPath_meas : Measurable fromPath :=
    Measurable.of_eval fun t =>
      ((measurable_pi_apply t).comp measurable_fst).prodMk
        (((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)).prodMk
          ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd)))
  -- path-space observable; OfRV turns 𝔼 into ∫ (· ∘ joint path)
  apply OfRV.eq.Integral.of.AEStronglyMeasurable_Map
    (f := fun p : (ℕ → ℝ) × (ℕ → S) × (ℕ → A) ↦
      (γ ^ (id : ℕ → ℕ)) @ fun t ↦
        (((γ ^ (id : ℕ → ℕ)) @ (X p.1 p.2.1 p.2.2)[t:]) •
          ∇[θ] Real.log (ℙ[M θ]((a t) = p.2.2 t | (s t) = p.2.1 t)).toReal))
  -- AEStronglyMeasurable of f: transport h₃ via fromPath + discrete gradient
  simp only [Dot.dot, Function.hPow_apply, id_eq]
  refine (StronglyMeasurable.tsum (L := SummationFilter.unconditional ℕ) fun t =>
    (StronglyMeasurable.smul
      (Measurable.tsum (L := SummationFilter.unconditional ℕ) fun k =>
        ((h₃ (t + k)).comp fromPath_meas).const_mul (γ ^ k)).stronglyMeasurable
      ((StronglyMeasurable.of_discrete (f := fun q : S × A =>
        gradient (fun θ' => Real.log (ℙ[M θ']((a t) = q.2 | (s t) = q.1)).toReal) θ)).comp_measurable
          (((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)).prodMk
            ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd))))).const_smul
      (γ ^ t)).aestronglyMeasurable


-- created on 2026-10-21
