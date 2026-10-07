import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Finset


/--
`𝔼[G(ω[t]) * f(ω[t+j])] = 𝔼[G(ω[t]) * Kf θ f j (ω[t])]` for bounded strongly measurable `f`, `G`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {f : ℝ × S × A → ℝ}
  {C : ℝ}
  {G : ℝ × S × A → ℝ}
  {CG : ℝ}
-- given
  (hf : StronglyMeasurable f)
  (hC : ∀ z, ‖f z‖ ≤ C)
  (hG : StronglyMeasurable G)
  (hCG : ∀ z, ‖G z‖ ≤ CG)
  (θ : Θ)
  (t j : ℕ) :
-- imply
  ∫ ω, G (ω t) * f (ω (t + j)) ∂(M θ) = ∫ ω, G (ω t) * M.Kf θ f j (ω t) ∂(M θ) := by
-- proof
  exact All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ j t (G := fun h => G (h ⟨t, mem_Iic.2 le_rfl⟩))
    (hG.comp_measurable (measurable_pi_apply _)) (CG := CG) (fun _ => hCG _)


-- created on 2026-10-07
