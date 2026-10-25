/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Abbrev.StatisticalMechanics.Code.Sharpness.RandomCurrent
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def incidentFlux (n : Current V) (x : V) : ℕ :=
  ∑ e ∈ G.edgeFinset.filter (fun e => x ∈ e), n e


noncomputable def sources (n : Current V) : Finset V :=
  Finset.univ.filter (fun x => Odd (incidentFlux G n x))

end Sharpness
end StatMech
