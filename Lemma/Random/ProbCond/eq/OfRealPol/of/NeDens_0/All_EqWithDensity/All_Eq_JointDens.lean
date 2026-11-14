import Lemma.Random.ProbCond.eq.OfRealPol.of.NeDens_0.All_EqWithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random
open scoped ENNReal.ToRealCoe
open IsPolicyTrajectory


/--
Real-valued continuous-action bridge: under absolute continuity of `law(a[t], s[t])`,
pointwise joint-density factorization into policy dens × state RN derivative, and a
positive finite state density at `x`, the conditional density coerces to the policy
probability:
`(ℙ[M θ](a[t] = u | s[t] = x) : ℝ) = M.policy.prob θ x u`.
-/
@[path]
private lemma main
  [μ : ReferenceMeasure 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ} {t : ℕ} {x : 𝒮} {u : 𝒜}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : DensityModel.IsPolicyTrajectory M r s a)
  (h₁ : DensityModel.AbsContJointAS M a s)
  (h₂ : (M θ).prob (a t, s t) (u, x) =
    ENNReal.ofReal (M.policy.prob θ x u) *
      ((M θ).map (s t)).rnDeriv (μ.measure : Measure 𝒮) x)
  (h₃ : ((M θ).map (s t)).rnDeriv (μ.measure : Measure 𝒮) x ≠ 0)
  (h₄ : ((M θ).map (s t)).rnDeriv (μ.measure : Measure 𝒮) x ≠ ⊤) :
-- imply
  have : SinglePSpace (M θ) (a t, s t) := h₀.singlePSpace_as (haj := h₁) θ t
  (ℙ[M θ]((a t) = u | (s t) = x) : ℝ) = M.policy.prob θ x u := by
-- proof
  intro hP
  have hENN :
    ℙ[M θ]((a t) = u | (s t) = x) =
      ENNReal.ofReal (M.policy.prob θ x u) :=
    ProbCond.eq.OfRealPol.of.NeDens_0.All_EqWithDensity (M := M) h₀ h₁ h₂ h₃ h₄
  rw [hENN, ENNReal.toReal_ofReal (M.policy.nonneg θ x u)]


-- created on 2026-10-21
-- updated on 2026-11-14
