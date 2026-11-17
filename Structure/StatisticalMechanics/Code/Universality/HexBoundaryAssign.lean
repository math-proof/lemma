/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryAssign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.Universality.HexFamilyAssign.Part3


public section

namespace StatMech.Universality

open Complex

open scoped BigOperators


structure HexRegion where
  
  width : ℝ
  
  slant : ℝ
  
  start : ℂ


end StatMech.Universality
