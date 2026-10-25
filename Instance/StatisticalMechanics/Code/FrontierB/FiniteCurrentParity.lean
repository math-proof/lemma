/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentMeasures
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSources.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentParity
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable instance instMeasurableSpaceCurrentParityFinset :
    MeasurableSpace (Finset (Sym2 V)) := ⊤

end StatMech.FrontierB
