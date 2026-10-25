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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part3


namespace StatMech.FrontierD

noncomputable section

def sixVertexContinuumDensityAt
    {a b : Real}
    (rho : C(Set.Icc a b × Real, Real))
    (t : Set.Icc a b) : C(Real, Real) :=
  rho.comp ⟨fun x => (t, x),
    continuous_const.prodMk continuous_id⟩

def sixVertexContinuumDensitySection
    {a b : Real} {N n : Nat}
    (rho : C(Set.Icc a b × Real, Real))
    (z : SixVertexBetheContinuationSpace a b N n) : C(Real, Real) :=
  sixVertexContinuumDensityAt rho ⟨z.1.1, z.2.1⟩

def sixVertexContinuationWeightedFiniteDensityGauge
    {a b : Real} (ha : 2 < a) (N n : Nat)
    (rho : C(Set.Icc a b × Real, Real))
    (z : SixVertexBetheContinuationSpace a b N n) : Real :=
  sixVertexWeightedFiniteDensityGauge (ha.trans_le z.2.1.1)
    N n z.1.2 (sixVertexContinuumDensitySection rho z)

end
end StatMech.FrontierD
