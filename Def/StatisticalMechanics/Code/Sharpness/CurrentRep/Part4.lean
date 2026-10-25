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
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part4
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000


namespace StatMech

namespace Sharpness

open StatMech.Ising


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def partitionJ (β : ℝ) (J : Sym2 V → ℝ) : ℝ :=
  ∑ s : ConfigSpace V, boltzmannJ G β J s


noncomputable def expectationJ (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) : ℝ :=
  (∑ s : ConfigSpace V, spinProd A s * boltzmannJ G β J s) / partitionJ G β J


end Sharpness
end StatMech
