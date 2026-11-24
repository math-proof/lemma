module
public import Theorem.StatisticalMechanics.Code.Universality.HexFamilyAssign.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex

open scoped BigOperators


variable {V : Type*} [DecidableEq V]


noncomputable def hexBdryAssign_decomp {D : HexDomain V} {P : D.InteriorPairing}
    {R : HexRegion} (A : HexRegionAssign D P R) : HexBoundaryDecomp D P :=
  A.toDecomp


end StatMech.Universality
