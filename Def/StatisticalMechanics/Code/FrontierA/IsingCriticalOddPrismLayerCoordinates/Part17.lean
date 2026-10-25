/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part16


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

def finiteExpMoment {E : Type*} [Fintype E]
    (w I : E -> Real) (r : Real) : Real :=
  ∑ x, w x * Real.exp (r * I x)

def finiteExpFirst {E : Type*} [Fintype E]
    (w I : E -> Real) (r : Real) : Real :=
  ∑ x, w x * (I x * Real.exp (r * I x))

def finiteExpSecond {E : Type*} [Fintype E]
    (w I : E -> Real) (r : Real) : Real :=
  ∑ x, w x * (I x ^ 2 * Real.exp (r * I x))

def finiteExpVarianceSkew {E : Type*} [Fintype E]
    (w I : E -> Real) (r : Real) : Real :=
  (finiteExpSecond w I r * finiteExpMoment w I r -
      finiteExpFirst w I r ^ 2) * finiteExpMoment w I (-r) ^ 2 -
    (finiteExpSecond w I (-r) * finiteExpMoment w I (-r) -
      finiteExpFirst w I (-r) ^ 2) * finiteExpMoment w I r ^ 2


end
end StatMech.FrontierA
