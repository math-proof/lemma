import sympy.stats.policy_trajectory
import sympy.functions.elementary.miscellaneous
import sympy.Basic
import Lemma.Random.MEq_Clip.of.All_Eq
import Lemma.Random.Integral_MulEq22.eq.MulProbIntegral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.NormClip.le.AbsR
import Lemma.Random.StronglyMeasurableClip
import Lemma.Real.LeNorm_Mul1.of.All_LeNorm
import Lemma.Real.StronglyMeasurable_Eq22
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`𝔼[1{s[t] = x ∧ a[t] = u} * r[t]] = Pr(s[t] = x) * π_θ(u | x) * 𝔼[(fun z ↦ clip z.1 (-M.env.R) M.env.R) | x, u]`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (u : A) :
-- imply
  ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * r t ω ∂(M θ) =
    (M θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u * ∫ ρ, clip (ρ, x, u).1 (-M.env.R) M.env.R ∂(M.env.reward (x, u)) := by
-- proof
  have h₁ : ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * r t ω ∂(M θ) =
      ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * clip (ω t).1 (-M.env.R) M.env.R ∂(M θ) :=
    integral_congr_ae ((MEq_Clip.of.All_Eq h₀ (M := M) θ t).mono fun ω h => by dsimp only; rw [h])
  have h₂ : ∀ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * clip (ω t).1 (-M.env.R) M.env.R =
      (if s t ω = x then (1:ℝ) else 0) *
        (fun z : ℝ × S × A => (if z.2.2 = u then (1:ℝ) else 0) * clip z.1 (-M.env.R) M.env.R) (ω t) := by
    intro ω
    have hs : s t ω = (ω t).2.1 := (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
    have ha : a t ω = (ω t).2.2 := (congrArg (·.2.2) (congrFun (h₀ t) ω)).symm
    simp only [hs, ha]
    by_cases h1 : (ω t).2.1 = x <;> by_cases h2 : (ω t).2.2 = u <;> simp [h1, h2]
  rw [h₁]
  simp_rw [h₂]
  rw [Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable h₀ (M := M) (g := fun z => (if z.2.2 = u then (1:ℝ) else 0) * clip z.1 (-M.env.R) M.env.R) ((Real.StronglyMeasurable_Eq22 u).mul (Random.StronglyMeasurableClip (M := M))) (LeNorm_Mul1.of.All_LeNorm (p := (fun z : ℝ × S × A => z.2.2 = u)) (NormClip.le.AbsR (M := M))) θ t x,
    Integral_MulEq22.eq.MulProbIntegral.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableClip (M := M)) (NormClip.le.AbsR (M := M)) θ x u, mul_assoc]


-- created on 2026-10-07
-- updated on 2026-10-12
