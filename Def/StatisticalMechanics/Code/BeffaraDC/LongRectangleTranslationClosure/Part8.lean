/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part6
import Instance.StatisticalMechanics.Code.BeffaraDC.LongRectangleTranslationClosure
open MeasureTheory SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


noncomputable def thinTranslationClosureCounterexampleConfig :
    TorusAmbientConfig 8 :=
  fun e =>
    match (torusEdgeCodeEquiv 8).symm e with
    | ((_, _), TorusEdgeOrientation.horizontal) => false
    | ((x, y), TorusEdgeOrientation.vertical) =>
        decide (x = 0 ∧ (y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4))

end StatMech.BeffaraDC
