/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricOffDiagonal.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityComponent
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedDensityCauchy
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuumUniqueness
import Mathlib.Algebra.Field.Periodic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexWeightedFiniteDensityDifference
    {c : Real} (hc : 2 < c) (N n : Nat) (p : Fin n → Real)
    (rho : C(Real, Real)) : C(Set.Icc (-Real.pi) Real.pi, Real) :=
  ⟨fun x : Set.Icc (-Real.pi) Real.pi =>
      sixVertexRootDensityWeight c x.1 *
        (sixVertexFiniteRootDensity c N n p x.1 - rho x.1), by
    apply Continuous.mul
    · unfold sixVertexRootDensityWeight sixVertexBetheIntegratingFactor
        sixVertexRootDensityScale
      fun_prop
    · apply Continuous.sub
      · exact (continuous_sixVertexFiniteRootDensity hc N n p).comp
          continuous_subtype_val
      · exact rho.continuous.comp continuous_subtype_val⟩

def sixVertexWeightedFiniteDensityGauge
    {c : Real} (hc : 2 < c) (N n : Nat) (p : Fin n → Real)
    (rho : C(Real, Real)) : Real :=
  ‖sixVertexWeightedFiniteDensityDifference hc N n p rho‖

end
end StatMech.FrontierD
