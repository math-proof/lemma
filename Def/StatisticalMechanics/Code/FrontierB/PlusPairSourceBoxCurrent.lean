/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusPairSourceBoxCurrent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundarySourceLaw.Part4
import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
open MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice

open StatMech.IsingFK


def boxSiteSucc {d n : ℕ} (x : StatMech.FK.boxVerts d n) :
    StatMech.FK.boxVerts d (n + 1) :=
  ⟨x.1, box_subset_succ d n x.2⟩

end StatMech.FrontierB
