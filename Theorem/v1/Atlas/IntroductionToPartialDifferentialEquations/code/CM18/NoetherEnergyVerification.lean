/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM18/NoetherEnergyVerification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM18.NoetherEnergy.Part2
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM18.NoetherEnergy


namespace CM18

example {n : ℕ} (Psi : FlowMap n) (phi : ScalarField n)
    (hphi : ContDiff ℝ ⊤ phi) (xt : Spacetime n) :
    deriv (fun eps => transformedField Psi phi eps xt) 0 =
      -(∑ alpha : Fin (n + 1), Psi.Y xt alpha * spacetimeGradient phi xt alpha) :=
  flow_deriv_scalar Psi phi hphi xt


#print axioms CM18.hasDerivAt_invJacobian_at_zero
#print axioms CM18.corollary_deriv_L_flow

example {n : ℕ} (Psi : FlowMap n) (xt : Spacetime n) (alpha mu : Fin (n + 1)) :
    HasDerivAt (fun eps => Psi.invJacobian eps xt alpha mu)
      (-fderiv ℝ (fun y => Psi.Y y alpha) xt (Pi.single mu 1)) 0 :=
  hasDerivAt_invJacobian_at_zero Psi xt alpha mu

example {n : ℕ} (Psi : FlowMap n) (xt : Spacetime n) (alpha mu : Fin (n + 1)) :
    DifferentiableAt ℝ (fun eps => Psi.invJacobian eps xt alpha mu) 0 :=
  (hasDerivAt_invJacobian_at_zero Psi xt alpha mu).differentiableAt

end CM18
