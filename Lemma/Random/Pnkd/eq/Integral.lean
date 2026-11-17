import Def.Dynamics.PolicyTrajectory.ContinuousAction
import Class.Dynamics.MarkovDecisionProcess
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


namespace PolicyGradient.Model

/-- n-step state transition of the continuous-action model: `Pnkd θ n x y = ℙ(s[n] = y | s[0] = x)`. -/
noncomputable def Pnkd
  {Θ 𝒮 𝒜 : Type*}
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  (M : Model Θ 𝒮 𝒜) [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M] (θ : Θ) (n : ℕ) (sₜ y : 𝒮) : ℝ :=
  ∫ z, M.Kf θ (fun w => if w.2.1 = y then (1 : ℝ) else 0) n z ∂(M.stageK θ sₜ)

end PolicyGradient.Model


/--
`Pnkd θ n x y = ∫ z, Kf θ (1{y = s z}) n z ∂(stageK θ x)` (bridge past the definition of `Model.Pnkd`).
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [ReferenceMeasure 𝒜] [DecidableEq 𝒮]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ)
  (n : ℕ)
  (sₜ y : 𝒮) :
-- imply
  M.Pnkd θ n sₜ y =
    ∫ z, M.Kf θ (fun w => if w.2.1 = y then (1:ℝ) else 0) n z ∂(M.stageK θ sₜ) :=
-- proof
  rfl


-- created on 2026-11-13
-- updated on 2026-11-17
