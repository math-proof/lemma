/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part6
import Def.StatisticalMechanics.Code.BeffaraDC.LongRectangleTranslationClosure.Part2
open MeasureTheory SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem bdcTorusThinCrossingTranslationClosureEvent_preimage
    (L alpha n : ℕ) [Fact (2 < L)] (s : Site 2) :
    torusAmbientTranslateConfig L s ⁻¹'
        bdcTorusThinCrossingTranslationClosureEvent L alpha n =
      bdcTorusThinCrossingTranslationClosureEvent L alpha n := by
  ext omega
  exact bdcTorusThinCrossingTranslationClosure_translate_iff
    L alpha n s omega


end StatMech.BeffaraDC
