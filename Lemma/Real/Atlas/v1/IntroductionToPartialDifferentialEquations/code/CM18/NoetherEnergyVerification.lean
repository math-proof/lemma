import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM18.NoetherEnergyVerification
open CM18


namespace CM18

/--
[corollary_deriv_L_flow_verified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM18/NoetherEnergyVerification.lean)
-/
@[path]
lemma corollary_deriv_L_flow_verified
  {n : ℕ}
  {L : MetricLagrangian n}
  {Psi : FlowMap n}
  {phi : ScalarField n}
  {m : Metric n}
  {x : Spacetime n}
-- given
  (hL_smooth : ContDiff ℝ 2 (fun p : ℝ × (Fin (n + 1) → ℝ) × (Fin (n + 1) → Fin (n + 1) → ℝ) => L p.1 p.2.1 p.2.2))
  (hphi : ContDiff ℝ ⊤ phi)
  (hm : ∀ alpha beta, ContDiff ℝ ⊤ (fun y => m y alpha beta)) :
-- imply
  deriv (fun eps => L (transformedField Psi phi eps x) (fun mu => transformedGradient Psi phi eps x mu) (fun mu nu => transformedMetric Psi m eps x mu nu)) 0 = -(deriv (fun v => L v (spacetimeGradient phi x) (m x)) (phi x)) * (∑ alpha : Fin (n + 1), Psi.Y x alpha * spacetimeGradient phi x alpha) - ∑ mu : Fin (n + 1), (fderiv ℝ (fun p => L (phi x) p (m x)) (spacetimeGradient phi x) (Pi.single mu 1)) * fderiv ℝ (fun y => ∑ alpha : Fin (n + 1), Psi.Y y alpha * spacetimeGradient phi y alpha) x (Pi.single mu 1) - ∑ mu : Fin (n + 1), ∑ nu : Fin (n + 1), dL_dm L phi m x mu nu * (∑ alpha : Fin (n + 1), m x alpha nu * fderiv ℝ (fun y => Psi.Y y alpha) x (Pi.single mu 1) + ∑ alpha : Fin (n + 1), m x mu alpha * fderiv ℝ (fun y => Psi.Y y alpha) x (Pi.single nu 1) + ∑ alpha : Fin (n + 1), Psi.Y x alpha * fderiv ℝ (fun y => m y mu nu) x (Pi.single alpha 1)) :=
-- proof
  corollary_deriv_L_flow L Psi phi m x hL_smooth hphi hm
#print axioms CM18.corollary_deriv_L_flow_verified

end CM18


-- created on 2026-10-23
