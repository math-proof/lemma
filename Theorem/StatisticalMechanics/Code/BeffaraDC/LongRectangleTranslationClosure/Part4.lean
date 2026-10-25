/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part6
import Def.StatisticalMechanics.Code.BeffaraDC.LongRectangleTranslationClosure.Part3
open MeasureTheory SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


@[simp] theorem torusReduceSite_bdcTorusCanonicalShift
    (L : ℕ) [NeZero L] (u : ZMod L × ZMod L) :
    torusReduceSite L (bdcTorusCanonicalShift u) = u := by
  apply Prod.ext
  · change (((u.1.val : ℕ) : ℤ) : ZMod L) = u.1
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  · change (((u.2.val : ℕ) : ℤ) : ZMod L) = u.2
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]


theorem torusAmbientTranslateConfig_eq_canonical
    (L : ℕ) [Fact (2 < L)] (t : Site 2)
    (omega : TorusAmbientConfig L) :
    torusAmbientTranslateConfig L t omega =
      torusAmbientTranslateConfig L
        (bdcTorusCanonicalShift (torusReduceSite L t)) omega := by
  funext e
  unfold torusAmbientTranslateConfig
  congr 1
  apply Subtype.ext
  change Sym2.map (torusSiteTranslateEquiv L t) e.1 =
    Sym2.map (torusSiteTranslateEquiv L
      (bdcTorusCanonicalShift (torusReduceSite L t))) e.1
  apply Sym2.map_congr
  intro z _hz
  apply Prod.ext <;>
    simp [torusSiteTranslateEquiv, bdcTorusCanonicalShift, torusReduceSite]


end StatMech.BeffaraDC
