import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM18.NoetherEnergy
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM18.NoetherEnergy
open CM18


/--
[flow_param_derivatives](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM18/VariationalNoether.lean)
-/
@[path]
lemma flow_param_derivatives
  {n : ℕ}
  {Psi : FlowMap n}
  {phi : ScalarField n}
  {m : Metric n}
  {mInv : InverseMetric n}
  {xt : Spacetime n}
-- given
  (hphi : ContDiff ℝ ⊤ phi)
  (hm : ∀ alpha beta, ContDiff ℝ ⊤ (fun y => m y alpha beta))
  (hmInv : ∀ alpha beta, ContDiff ℝ ⊤ (fun y => mInv y alpha beta)) :
-- imply
  (deriv (fun eps => transformedField Psi phi eps xt) 0 = -(∑ alpha : Fin (n + 1), Psi.Y xt alpha * spacetimeGradient phi xt alpha)) ∧ (∀ mu : Fin (n + 1), deriv (fun eps => transformedGradient Psi phi eps xt mu) 0 = -fderiv ℝ (fun y => ∑ alpha : Fin (n + 1), Psi.Y y alpha * spacetimeGradient phi y alpha) xt (Pi.single mu 1)) ∧ (∀ mu nu : Fin (n + 1), deriv (fun eps => transformedMetric Psi m eps xt mu nu) 0 = -(∑ alpha : Fin (n + 1), m xt alpha nu * fderiv ℝ (fun y => Psi.Y y alpha) xt (Pi.single mu 1) + ∑ alpha : Fin (n + 1), m xt mu alpha * fderiv ℝ (fun y => Psi.Y y alpha) xt (Pi.single nu 1) + ∑ alpha : Fin (n + 1), Psi.Y xt alpha * fderiv ℝ (fun y => m y mu nu) xt (Pi.single alpha 1))) ∧ (∀ mu nu : Fin (n + 1), deriv (fun eps => transformedInverseMetric Psi mInv eps xt mu nu) 0 = ∑ alpha : Fin (n + 1), mInv xt alpha nu * fderiv ℝ (fun y => Psi.Y y mu) xt (Pi.single alpha 1) + ∑ alpha : Fin (n + 1), mInv xt mu alpha * fderiv ℝ (fun y => Psi.Y y nu) xt (Pi.single alpha 1) - ∑ alpha : Fin (n + 1), Psi.Y xt alpha * fderiv ℝ (fun y => mInv y mu nu) xt (Pi.single alpha 1)) ∧ (deriv (fun eps => Matrix.det (Matrix.of (fun mu nu => Psi.invJacobian eps xt mu nu))) 0 = -(∑ alpha : Fin (n + 1), fderiv ℝ (fun y => Psi.Y y alpha) xt (Pi.single alpha 1))) := by
-- proof
  exact ⟨
    flow_deriv_scalar Psi phi hphi xt,
    fun mu => flow_deriv_gradient Psi phi hphi xt mu,
    fun mu nu => flow_deriv_metric Psi m xt mu nu hm,
    fun mu nu => flow_deriv_inverse_metric Psi mInv xt mu nu hmInv,
    flow_deriv_det_invJacobian Psi xt⟩


-- created on 2026-10-23
