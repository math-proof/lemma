/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover.Part6
import Theorem.StatisticalMechanics.Code.FK.FKG
import Def.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.Universality


@[simp] theorem torusAmbientPMF_apply (L : ℕ) [Fact (2 < L)]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : TorusAmbientConfig L) :
    torusAmbientPMF L hp hp1 hq omega =
      ENNReal.ofReal (torusAmbientProbability L p q omega) :=
  PMF.ofFintype_apply _ _


end StatMech.BeffaraDC
