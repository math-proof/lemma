module
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhysical.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part6
public import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSignedPhysical.Part4
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


noncomputable def triangularTorusNormalizedLinearSector
    (L : Nat) [Fact (2 < L)] (J1 J2 J3 : Real)
    (chi : Fin 2 × Fin 2) : Real :=
  (Real.cosh J1 * Real.cosh J2 * Real.cosh J3) ^ (L * L) *
    triangularTorusWeightedLinearCharacterSum L
      (triangularTorusRealEdgeWeight L
        (Real.tanh J1) (Real.tanh J2) (Real.tanh J3)) chi

end StatMech.FrontierA
