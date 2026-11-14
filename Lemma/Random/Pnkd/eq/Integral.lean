import Def.Dynamics.PolicyTrajectory.ContinuousAction
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel


namespace PolicyGradient.DensityModel

/-- n-step state transition of the continuous-action model: `Pnkd θ n x y = ℙ(s[n] = y | s[0] = x)`. -/
noncomputable def Pnkd
  {Θ 𝒮 𝒜 : Type*}
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  (M : DensityModel Θ 𝒮 𝒜) (θ : Θ) (n : ℕ) (x y : 𝒮) : ℝ :=
  ∫ z, M.Kf θ (fun w => if w.2.1 = y then (1 : ℝ) else 0) n z ∂(M.stageK θ x)

end PolicyGradient.DensityModel


/--
`Pnkd θ n x y = ∫ z, Kf θ (1{y = s z}) n z ∂(stageK θ x)` (bridge past the definition of `DensityModel.Pnkd`).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : DensityModel Θ 𝒮 𝒜}
-- given
  (θ : Θ)
  (n : ℕ)
  (x y : 𝒮) :
-- imply
  M.Pnkd θ n x y =
    ∫ z, M.Kf θ (fun w => if w.2.1 = y then (1:ℝ) else 0) n z ∂(M.stageK θ x) :=
-- proof
  rfl


-- created on 2026-11-13
