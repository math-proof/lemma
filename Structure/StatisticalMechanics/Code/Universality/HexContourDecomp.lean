/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexContourDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexBoundary.Part4


namespace StatMech.Universality

open Complex

open scoped BigOperators


structure HexSide {V : Type*} [DecidableEq V] (D : HexDomain V) where
  
  cells : Finset (HexIncidence V)
  
  dir : ℂ
  
  dirEq : ∀ e ∈ cells, D.mid e.vtx e.edge - D.pos e.vtx = dir

end StatMech.Universality
