import Def.Dynamics.PolicyTrajectory.Gradient
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model


namespace PolicyGradient.Model

/-- n-step discounted occupancy weight of state `y` starting from `x`. -/
noncomputable def Pn
  {Θ S A : Type*}
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  (M : Model Θ S A) (θ : Θ) (n : ℕ) (x y : S) : ℝ :=
  ∫ z, M.Kf θ (fun w => if w.2.1 = y then (1 : ℝ) else 0) n z ∂(M.stageK θ x)

end PolicyGradient.Model


/--
`Pn θ n x y = ∫ z, Kf θ (1{y = s z}) n z ∂(stageK θ x)` (bridge past the `𝔼` sugar on `Model.Pn`).
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (n : ℕ)
  (x y : S) :
-- imply
  M.Pn θ n x y =
    ∫ z, M.Kf θ (fun w => if w.2.1 = y then (1:ℝ) else 0) n z ∂(M.stageK θ x) :=
-- proof
  rfl


-- created on 2026-10-11
-- updated on 2026-11-08
