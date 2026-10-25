/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/TwoReplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Abbrev.StatisticalMechanics.Code.Ising.TwoReplica
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (E : Finset (Sym2 V))


def incidentFlux (n : Current V) (x : V) : ℕ :=
  ∑ e ∈ E.filter (fun e => x ∈ e), n e


def sources (n : Current V) : Finset V :=
  Finset.univ.filter (fun x => Odd (incidentFlux E n x))

end Ising
end StatMech
