/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailConvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCyclicQuadrature
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheIntegratingFactor_add_two_pi
    (c x : Real) :
    sixVertexBetheIntegratingFactor c (x + 2 * Real.pi) =
      sixVertexBetheIntegratingFactor c x := by
  unfold sixVertexBetheIntegratingFactor
  rw [Real.cos_add_two_pi]

theorem sixVertexThetaDerivativeDenominator_add_two_pi_left
    (c x y : Real) :
    sixVertexThetaDerivativeDenominator c (x + 2 * Real.pi) y =
      sixVertexThetaDerivativeDenominator c x y := by
  unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem sixVertexThetaDerivativeDenominator_add_two_pi_right
    (c x y : Real) :
    sixVertexThetaDerivativeDenominator c x (y + 2 * Real.pi) =
      sixVertexThetaDerivativeDenominator c x y := by
  unfold sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
  rw [Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem sixVertexRootDensityKernel_add_two_pi_left
    (c x y : Real) :
    sixVertexRootDensityKernel c (x + 2 * Real.pi) y =
      sixVertexRootDensityKernel c x y := by
  unfold sixVertexRootDensityKernel
  rw [sixVertexBetheIntegratingFactor_add_two_pi,
    sixVertexThetaDerivativeDenominator_add_two_pi_left]

theorem sixVertexRootDensityKernel_add_two_pi_right
    (c x y : Real) :
    sixVertexRootDensityKernel c x (y + 2 * Real.pi) =
      sixVertexRootDensityKernel c x y := by
  unfold sixVertexRootDensityKernel
  rw [sixVertexBetheIntegratingFactor_add_two_pi,
    sixVertexThetaDerivativeDenominator_add_two_pi_right]

theorem periodic_sixVertexRootDensityKernel_right (c x : Real) :
    Function.Periodic (sixVertexRootDensityKernel c x) (2 * Real.pi) :=
  fun y => sixVertexRootDensityKernel_add_two_pi_right c x y

theorem sixVertexFiniteRootDensity_add_two_pi
    (c : Real) (N n : Nat) (p : Fin n → Real) (x : Real) :
    sixVertexFiniteRootDensity c N n p (x + 2 * Real.pi) =
      sixVertexFiniteRootDensity c N n p x := by
  unfold sixVertexFiniteRootDensity
  congr 3
  apply Finset.sum_congr rfl
  intro k _
  rw [sixVertexThetaDerivativeDenominator_add_two_pi_left]

theorem periodic_sixVertexFiniteRootDensity
    (c : Real) (N n : Nat) (p : Fin n → Real) :
    Function.Periodic (sixVertexFiniteRootDensity c N n p)
      (2 * Real.pi) :=
  sixVertexFiniteRootDensity_add_two_pi c N n p

end
end StatMech.FrontierD
