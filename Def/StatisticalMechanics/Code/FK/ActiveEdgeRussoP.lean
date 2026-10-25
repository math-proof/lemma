/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveEdgeRussoP.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.ActiveEdges.Part4
import Theorem.StatisticalMechanics.Code.FK.RussoDerivative.Part5
open scoped BigOperators
open Finset


namespace StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def activePScore (p : ℝ) (ω : ConfigSpace G.edgeSet) : ℝ :=
  ∑ e : G.edgeSet, (OSSS.Lindeberg.coord e ω - p)

end StatMech.FK
