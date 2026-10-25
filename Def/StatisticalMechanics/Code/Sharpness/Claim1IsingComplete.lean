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
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingComplete
open SimpleGraph Finset
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def claim1Context (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V)
    (P : Current V → Prop) [DecidablePred P] (B D : Finset V)
    (bd : ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) ×
      ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)) : ℝ :=
  (if sources G (ofEdgeFun G (bFull G S bd.1)) = B
      then weight G β J (ofEdgeFun G (bFull G S bd.1)) else 0) *
    (if sources G (ofEdgeFun G (bFull G S bd.2)) = D
      then weight G β J (ofEdgeFun G (bFull G S bd.2)) else 0) *
    (if P (fun e => ofEdgeFun G (bFull G S bd.1) e +
        ofEdgeFun G (bFull G S bd.2) e) then 1 else 0)


noncomputable def pairCutEquiv (S : Finset V) :
    ((({i : ↥G.edgeFinset // isIn G S i} → ℕ) ×
        ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)) ×
      (({i : ↥G.edgeFinset // isIn G S i} → ℕ) ×
        ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ))) ≃
    ((({i : ↥G.edgeFinset // isIn G S i} → ℕ) ×
        ({i : ↥G.edgeFinset // isIn G S i} → ℕ)) ×
      (({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) ×
        ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ))) where
  toFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  invFun p := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  left_inv := by rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
  right_inv := by rintro ⟨⟨a, c⟩, ⟨b, d⟩⟩; rfl


end Sharpness
end StatMech
