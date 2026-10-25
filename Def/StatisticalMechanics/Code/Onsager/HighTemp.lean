/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/HighTemp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KWSelfDuality.Part4
open scoped BigOperators
open Finset


namespace StatMech

namespace Onsager

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ons_Z (β : ℝ) : ℝ := isingZ G β 0


noncomputable def ons_X (x : ℝ) : ℝ :=
  ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, x ^ F.card


end Onsager
end StatMech
