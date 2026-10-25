/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConcreteRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexPairingMaps.Part4
import Def.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part2


namespace StatMech.Universality

open Complex

open Function

open HexWalk

open scoped BigOperators


theorem hexConcrete_v0_canon (a : ℂ) (h0 : ℤ) :
    hexConcreteV0 a h0 = a + (((1 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  unfold hexConcreteV0; push_cast; ring


theorem hexConcrete_vq_canon (a : ℂ) (h0 : ℤ) :
    hexConcreteVq a h0 = a + (((1 : ℝ) : ℂ) + ((-2 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  unfold hexConcreteVq
  rw [show (h0 + (-1) : ℤ) = h0 - 1 by ring, hexConcrete_halfStep_sub]
  push_cast; ring


theorem hexConcrete_vr_canon (a : ℂ) (h0 : ℤ) :
    hexConcreteVr a h0 = a + (((3 : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * hexOmega) * halfStep h0 := by
  unfold hexConcreteVr
  rw [hexConcrete_halfStep_add, hexConcrete_omega_cubic]
  push_cast; ring


theorem hexConcrete_verts_distinct (a : ℂ) (h0 : ℤ) :
    hexConcreteV0 a h0 ≠ hexConcreteVq a h0
      ∧ hexConcreteV0 a h0 ≠ hexConcreteVr a h0
      ∧ hexConcreteVq a h0 ≠ hexConcreteVr a h0 := by
  have hs : halfStep h0 ≠ 0 := hexConcrete_halfStep_ne h0
  rw [hexConcrete_v0_canon, hexConcrete_vq_canon, hexConcrete_vr_canon]
  refine ⟨?_, ?_, ?_⟩
  · exact hexConcrete_mid_ne a (halfStep h0) hs 1 0 1 (-2) (by norm_num)
  · exact hexConcrete_mid_ne a (halfStep h0) hs 1 0 3 2 (by norm_num)
  · exact hexConcrete_mid_ne a (halfStep h0) hs 1 (-2) 3 2 (by norm_num)


end StatMech.Universality
