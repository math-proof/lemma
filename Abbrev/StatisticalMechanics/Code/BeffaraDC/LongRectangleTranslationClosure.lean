/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTranslationClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part6
import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTranslationClosure.Part4
open MeasureTheory SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


abbrev BdcLongRectangleTorusTranslationIndex (L alpha : ℕ) :=
  (ZMod L × ZMod L) × BdcLongRectangleIndex alpha


end StatMech.BeffaraDC
