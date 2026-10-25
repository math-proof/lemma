/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBoundaryUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexContourDecomp.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBoundConcrete.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond


namespace StatMech.Universality

open Complex

open scoped BigOperators


def hexUncondPairing (a : ℂ) (h0 : ℤ) : (hexUncondDomain a h0).InteriorPairing where
  interior := ∅
  pair := id
  pair_mem := by intro e he; simp at he
  pair_invol := by intro e he; simp at he
  pair_ne := by intro e he; simp at he
  cancel := by intro e he; simp at he


end StatMech.Universality
