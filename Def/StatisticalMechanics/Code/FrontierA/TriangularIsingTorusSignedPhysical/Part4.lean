module
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhysical.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part6
public import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSignedPhysical.Part3
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


noncomputable def triangularTorusSeamTwistedCoupling
    (L : Nat) (J1 J2 J3 : Real) (chi : Fin 2 × Fin 2) :
    Sym2 (ZMod L × ZMod L) → Real := fun edge =>
  triangularTorusSeamTwistSign L chi edge *
    triangularTorusRealEdgeWeight L J1 J2 J3 edge

end StatMech.FrontierA
