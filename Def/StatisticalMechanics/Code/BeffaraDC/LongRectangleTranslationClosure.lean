module
public import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part6
public import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTranslationClosure
open MeasureTheory SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


def bdcTorusThinCrossingTranslationClosure
    (L alpha n : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) : Prop :=
  ∃ t : Site 2,
    bdcTorusThinCrossing L alpha n
      (torusAmbientTranslateConfig L t omega)


end StatMech.BeffaraDC
