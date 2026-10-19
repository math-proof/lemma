import Lemma.Random.RealPreimageS_Add_1.ne.Zero.of.NeMulProbT_0.Ne0Real_Preimage
import Lemma.Random.V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
On a reachable state `x`: `π_θ(u | x) * (T(x, u, y) * V θ γ (t+1) y) = π_θ(u | x) * (T(x, u, y) * ∑' k, γ ^ k * W θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k y)`.
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
  (θ : Θ)
  (t : ℕ)
  (x : S)
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (hP : (M θ).real (s t ⁻¹' {x}) ≠ 0)
  (u : A)
  (y : S) :
-- imply
  let V (θ : Θ) (t : ℕ) (x : S) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x);
  M.policy.prob θ x u * ((M.env.trans (x, u)).real {y} * V θ (t + 1) y) =
    M.policy.prob θ x u * ((M.env.trans (x, u)).real {y} * ∑' k, γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ y)) := by
-- proof
  intro Vθ
  if hz : M.policy.prob θ x u * (M.env.trans (x, u)).real {y} = 0 then
    rw [← mul_assoc, ← mul_assoc, hz, zero_mul, zero_mul]
  else
    have hV : Vθ θ (t + 1) y = ∑' k, γ ^ k * ∫ z, M.Kf θ (fun z ↦ clip z.1 (-M.env.R) M.env.R) k z ∂(M.stageK θ y) :=
      V.eq.TSum_MulPowWRc.of.Ne0Real_Preimage.In_Ico (M := M) θ (t + 1) y h₀ h₁
        (RealPreimageS_Add_1.ne.Zero.of.NeMulProbT_0.Ne0Real_Preimage (M := M) θ t x u y h₁ hP hz)
    rw [hV]


-- created on 2026-10-07
-- updated on 2026-10-12
