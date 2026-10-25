/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexContourDefs.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

variable {V : Type*} [DecidableEq V]


noncomputable def hexFiniteStripRaw (Fa : ℝ)
    (alphaRest betaSum epsSum epsbarSum : ℂ) : ℂ :=
  -((Fa : ℂ) + alphaRest) + betaSum
    + hbi_j * epsSum + (starRingEnd ℂ) hbi_j * epsbarSum


end StatMech.Universality
