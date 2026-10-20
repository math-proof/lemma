import Lemma.Random.V.eq.Vc.of.Ne0Real_Preimage.In_Ico
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random


/--
On a reachable state (`Pr(s[t] = x) ≠ 0`), the closed-form `Vc` equals the usual state value `V`: `Vc θ γ x = V θ γ t x`.
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
  (h₂ : (M θ).real (s t ⁻¹' {x}) ≠ 0) :
-- imply
  let Vθ (θ : Θ) (t : ℕ) (x : S) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x);
  M.Vc θ γ x = Vθ θ t x := by
-- proof
  intro Vθ
  apply Eq.symm
  apply V.eq.Vc.of.Ne0Real_Preimage.In_Ico (M := M) θ t x h₀ h₁ h₂


-- created on 2026-10-20
