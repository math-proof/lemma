/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part2


namespace StatMech.Universality

open Filter Topology

open scoped Topology BigOperators


structure HexContourEmb (W I : Type*) where
  
  wtSAW : W → ℝ
  
  emb : I → W
  
  emb_inj : Function.Injective emb
  
  wtSAW_nn : ∀ w, 0 ≤ wtSAW w

end StatMech.Universality
