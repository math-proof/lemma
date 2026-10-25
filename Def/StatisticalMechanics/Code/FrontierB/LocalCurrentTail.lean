/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/LocalCurrentTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.BoxCurrentLaws.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWSelfDuality.Part4
import Theorem.StatisticalMechanics.Code.FrontierB.LocalCurrentTail
open MeasureTheory
open scoped ENNReal BigOperators


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

def doubledEdgeCoupling (J : Sym2 V → ℝ) (e : Sym2 V) : Sym2 V → ℝ :=
  fun f => if f = e then 2 * J f else J f


end StatMech.FrontierB
