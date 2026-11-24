module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part8
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheJacobianSign
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
open Finset Filter Topology Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheJacobianStability.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheJacobianMatrix (N n : Nat) (c : Real)
    (p : Fin n → Real) : Matrix (Fin n) (Fin n) Real := fun j k =>
  if j = k then
    (N : Real) + ∑ l ∈ Finset.univ.erase j,
      4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p l) /
        sixVertexThetaDerivativeDenominator c (p j) (p l)
  else
    -4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p j) /
      sixVertexThetaDerivativeDenominator c (p j) (p k)

end
end StatMech.FrontierD
