import Lemma.Random.MEq_Clip.of.All_Eq
import Lemma.Random.Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral_MulEq12AndEq22.eq.MulMulRealProb
import Lemma.Random.Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.NormClip.le.AbsR
import Lemma.Random.StronglyMeasurableClip
import Lemma.Real.StronglyMeasurable_Eq12AndEq22
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Real


/--
`𝔼[1{s[t] = x ∧ a[t] = u} * r[t+j+1]] = Pr(s[t] = x) * π_θ(u | x) * ∑ y, T(x, u, y) * W θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) j y`.
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
  (t j : ℕ)
  (x : S)
  (u : A) :
-- imply
  ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * r (t + (j + 1)) ω ∂(M θ) =
    (M θ).real (s t ⁻¹' {x}) * M.policy.prob θ x u * ∑ y, (M.env.trans (x, u)).real {y} * ∫ w, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) j w ∂(M.stageK θ y) := by
-- proof
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₀ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  have hrc : ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * r (t + (j + 1)) ω ∂(M θ) =
      ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * clip (ω (t + (j + 1))).1 (-M.env.R) M.env.R ∂(M θ) :=
    integral_congr_ae ((MEq_Clip.of.All_Eq h₀ (M := M) θ (t + (j + 1))).mono fun ω h => by dsimp only; rw [h])
  rw [hrc]
  refine (Integral_Mul.eq.Integral_Mul_Kf.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableClip (M := M)) (NormClip.le.AbsR (M := M)) (Real.StronglyMeasurable_Eq12AndEq22 x u) (Norm_1.le.One) θ t (j + 1)).trans ?_
  simp_rw [Kf.eq.Sum_MulTW.of.All_LeNorm.StronglyMeasurable (M := M) (Random.StronglyMeasurableClip (M := M)) (NormClip.le.AbsR (M := M)) θ j]
  apply Integral_MulEq12AndEq22.eq.MulMulRealProb (M := M) h₀ θ t x u (fun x' u' => ∑ y, (M.env.trans (x', u')).real {y} * ∫ w, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) j w ∂(M.stageK θ y))


-- created on 2026-10-07
-- updated on 2026-10-12
