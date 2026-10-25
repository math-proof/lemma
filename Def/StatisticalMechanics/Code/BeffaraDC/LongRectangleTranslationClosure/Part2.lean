/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part6
import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTranslationClosure.Part2
open MeasureTheory SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


def bdcTorusThinCrossingTranslationClosureEvent
    (L alpha n : ℕ) [Fact (2 < L)] :
    Set (TorusAmbientConfig L) :=
  {omega | bdcTorusThinCrossingTranslationClosure L alpha n omega}


end StatMech.BeffaraDC
