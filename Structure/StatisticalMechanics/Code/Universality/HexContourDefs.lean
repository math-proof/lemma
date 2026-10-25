/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryAssign.Part3
import Def.StatisticalMechanics.Code.Universality.HexContourDefs


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


structure HexContourSides where
  
  bottom : Set ℂ
  
  slantPlus : Set ℂ
  
  slantMinus : Set ℂ
  
  top : Set ℂ


end StatMech.Universality
