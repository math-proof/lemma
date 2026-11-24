module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
public import Mathlib.Topology.UnitInterval
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredTensorTentRegularity.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Metric Set

open scoped unitInterval

noncomputable section

def complexBilinearTwoByTwo
    (a00 a10 a20 a01 a11 a21 a02 a12 a22 : Complex)
    (x y : Real) : Complex :=
  if y <= 1 then
    complexBilinearHorizontalStrip a00 a10 a20 a01 a11 a21 x y
  else
    complexBilinearHorizontalStrip a01 a11 a21 a02 a12 a22 x (y - 1)


end
end StatMech.Universality
