/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.BeffaraDC.ActiveRussoHamming
import Theorem.StatisticalMechanics.Code.FK.ComparisonHolley.Part3
import Theorem.StatisticalMechanics.Code.BeffaraDC.ActiveInfluence
open scoped BigOperators


namespace StatMech.BeffaraDC

open Finset

open StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def activeInfluence (p q : ℝ)
    (A : Set (ConfigSpace G.edgeSet)) (e : G.edgeSet) : ℝ :=
  let m := openMarginal (activeProb G (fun _ => p) q) e
  activeCov G (fun _ => p) q (A.indicator fun _ => (1 : ℝ))
    (OSSS.Lindeberg.coord e) / (m * (1 - m))

end StatMech.BeffaraDC
