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
  [ReferenceMeasure S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {θ : Θ} {t : ℕ} {x : S} {u : A}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : DensityModel.IsPolicyTrajectory M r s a)
  (h₁ : DensityModel.AbsContJointAS M a s)
  (h₂ : (M θ).prob (a t, s t) (u, x) =
    ENNReal.ofReal (M.policy.prob θ x u) *
      ((M θ).map (s t)).rnDeriv (ReferenceMeasure.measure : Measure S) x)
  (h₃ : ((M θ).map (s t)).rnDeriv (ReferenceMeasure.measure : Measure S) x ≠ 0)
  (h₄ : ((M θ).map (s t)).rnDeriv (ReferenceMeasure.measure : Measure S) x ≠ ⊤) :
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
