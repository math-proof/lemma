/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice


namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


structure HexWalk where
  
  startMid : ℂ
  
  h0 : ℤ
  

  turns : List ℤ

end StatMech.Universality
