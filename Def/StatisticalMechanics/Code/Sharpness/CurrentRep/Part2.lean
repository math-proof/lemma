/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CurrentRep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part2
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000


namespace StatMech

namespace Sharpness

open StatMech.Ising


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def currentSum (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) : ℝ :=
  ∑' m : ↥G.edgeFinset → ℕ,
    if sources G (ofEdgeFun G m) = A then weight G β J (ofEdgeFun G m) else 0


noncomputable def gEdge (β : ℝ) (J : Sym2 V → ℝ) (s : ConfigSpace V)
    (e : Sym2 V) (k : ℕ) : ℝ := (β * J e) ^ k * (bond s e) ^ k / k.factorial


end Sharpness
end StatMech
