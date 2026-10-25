/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingFull.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingComplete.Part2
open SimpleGraph Finset
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


open FluxEdgeCopy


noncomputable def gatedSourcePairSum (β : ℝ) (J : Sym2 V → ℝ)
    (A B : Finset V) (P : Current V → Prop) [DecidablePred P] : ℝ :=
  ∑' pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ),
    (if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0) *
      (if sources G (ofEdgeFun G pq.2) = B then weight G β J (ofEdgeFun G pq.2) else 0) *
      (if P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) then 1 else 0)

end Sharpness
end StatMech
