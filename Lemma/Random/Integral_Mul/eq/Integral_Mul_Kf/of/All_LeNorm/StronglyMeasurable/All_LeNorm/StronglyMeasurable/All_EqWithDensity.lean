import Lemma.Random.All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Finset


/--
`𝔼[G(ω[t]) * f(ω[t+j])] = 𝔼[G(ω[t]) * Kf θ f j (ω[t])]` for bounded strongly measurable `f`, `G`
(continuous-action model).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {f : ℝ × 𝒮 × 𝒜 → ℝ}
  {C : ℝ}
  {G : ℝ × 𝒮 × 𝒜 → ℝ}
  {CG : ℝ}
-- given
  (hf : StronglyMeasurable f)
  (hC : ∀ z, ‖f z‖ ≤ C)
  (hG : StronglyMeasurable G)
  (hCG : ∀ z, ‖G z‖ ≤ CG)
  (θ : Θ)
  (t j : ℕ) :
-- imply
  ∫ ω, G (ω t) * f (ω (t + j)) ∂(M θ) = ∫ ω, G (ω t) * M.Kf θ f j (ω t) ∂(M θ) :=
-- proof
  All_EqIntegral_MulGIntegral_MulGKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
    (M := M) hf hC θ j t
    (G := fun h => G (h ⟨t, mem_Iic.2 le_rfl⟩))
    (hG.comp_measurable (measurable_pi_apply _)) (CG := CG) (fun _ => hCG _)


-- created on 2026-11-13
