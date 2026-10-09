import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.RealPreimageS_Add_1.ne.Zero.of.NeMulProbT_0.Ne0Real_Preimage
import Lemma.Random.V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
On a reachable state `x`: `π_θ(u | x) * (T(x, u, y) * V θ γ (t+1) y) = π_θ(u | x) * (T(x, u, y) * ∑' k, γ ^ k * W θ rc k y)`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (hγ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (hP : (M θ).real (s t ⁻¹' {x}) ≠ 0)
  (u : A)
  (y : S) :
-- imply
  M.pol.prob θ x u * (M.T x u y * M.V r s θ γ (t + 1) y) =
    M.pol.prob θ x u * (M.T x u y * ∑' k, γ ^ k * M.W θ M.rc k y) := by
-- proof
  if hz : M.pol.prob θ x u * M.T x u y = 0 then
    rw [← mul_assoc, ← mul_assoc, hz, zero_mul, zero_mul]
  else
    rw [V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico (M := M) θ (t + 1) y hγ h₁ (RealPreimageS_Add_1.ne.Zero.of.NeMulProbT_0.Ne0Real_Preimage (M := M) h₁ θ t x u y hP hz)]


-- created on 2026-10-07
