/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABCouplingReindex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABClusterCondition
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
open Finset SimpleGraph


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def abcrEndpointSum (F : V → ℝ) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun x y => F x + F y, fun x y => by ring⟩

end Sharpness
end StatMech
