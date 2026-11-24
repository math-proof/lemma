module
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhysical.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part6
public import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSignedPhysical.Part6
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


noncomputable def triangularKacWardPhaseRoot : Complex :=
  Classical.choose
    (IsAlgClosed.exists_pow_nat_eq Complex.I (by norm_num : 0 < 4))

end StatMech.FrontierA
