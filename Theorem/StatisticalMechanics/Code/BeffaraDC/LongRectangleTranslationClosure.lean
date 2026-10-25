/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part6
open MeasureTheory SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem translateConfig_add (t s : Site 2)
    (omega : ConfigSpace (Sym2 (Site 2))) :
    translateConfig t (translateConfig s omega) =
      translateConfig (t + s) omega := by
  funext e
  unfold translateConfig
  rw [Sym2.map_map]
  congr 1
  apply Sym2.map_congr
  intro z _hz
  ext i
  simp [add_assoc]


theorem torusAmbientTranslateConfig_add
    (L : ℕ) [Fact (2 < L)] (t s : Site 2)
    (omega : TorusAmbientConfig L) :
    torusAmbientTranslateConfig L t
        (torusAmbientTranslateConfig L s omega) =
      torusAmbientTranslateConfig L (t + s) omega := by
  apply torusPlanarPullback_injective L
  rw [torusPlanarPullback_translate, torusPlanarPullback_translate,
    torusPlanarPullback_translate, translateConfig_add]


@[simp] theorem torusAmbientTranslateConfig_zero
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    torusAmbientTranslateConfig L 0 omega = omega := by
  apply torusPlanarPullback_injective L
  rw [torusPlanarPullback_translate, translateConfig_zero]


end StatMech.BeffaraDC
