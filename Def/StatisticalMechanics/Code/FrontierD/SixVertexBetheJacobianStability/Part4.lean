module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheLocalAnalytic.Part8
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheJacobianSign
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheJacobianStability.Part3
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

def sixVertexBetheSymmetricHalfJacobianMatrix
    (N m : Nat) (c : Real) (p : Fin (m + m) → Real) :
    Matrix (Fin m) (Fin m) Real := fun j k =>
  sixVertexBetheJacobianMatrix N (m + m) c p
      (sixVertexFirstHalfIndex m j) (sixVertexFirstHalfIndex m k) -
    sixVertexBetheJacobianMatrix N (m + m) c p
      (sixVertexFirstHalfIndex m j) (sixVertexReflectedHalfIndex m k)


end
end StatMech.FrontierD
