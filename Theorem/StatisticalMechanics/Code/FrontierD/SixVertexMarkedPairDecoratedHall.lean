module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairFractionalTransport.Part3
public import Theorem.StatisticalMechanics.Code.Foundations.FiniteBidegreeHall
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall
open Finset Matrix Polynomial


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairDecoratedHall.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

theorem sixVertexMarkedPairMultiplicity_eq_natCast
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (homega : omega.IceRule) (heta : eta.IceRule) (k : Nat) :
    sixVertexMarkedPairMultiplicity omega eta k =
      (sixVertexMarkedPairMultiplicityNat omega eta k : Real) := by
  unfold sixVertexMarkedPairMultiplicity
  rw [sixVertexTorusMarkedWeight_eq_pow omega homega,
    sixVertexTorusMarkedWeight_eq_pow eta heta, ← pow_add,
    coeff_two_add_X_pow]
  simp [sixVertexMarkedPairMultiplicityNat]


end
end StatMech.FrontierD
