/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11


namespace StatMech.Universality

open List


structure HexBridge where
  
  width : ℕ
  
  width_pos : 0 < width
  
  content : List ℤ
  
  content_ne : content ≠ []

end StatMech.Universality
