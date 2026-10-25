/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempSimon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSimon.Part5
open Finset SimpleGraph
open scoped BigOperators symmDiff


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def highTempSourceSubgraphs (E : Finset (Sym2 V))
    (A : Finset V) : Finset (Finset (Sym2 V)) :=
  E.powerset.filter (fun F => HasOddBoundary F A)

noncomputable def highTempSourceSum (E : Finset (Sym2 V))
    (t : Sym2 V → ℝ) (A : Finset V) : ℝ :=
  ∑ F ∈ highTempSourceSubgraphs E A, ∏ e ∈ F, t e

end Sharpness
end StatMech
