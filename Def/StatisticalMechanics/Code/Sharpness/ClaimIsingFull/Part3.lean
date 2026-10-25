/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ClaimIsingFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsing.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part2
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def contextSummand (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (P : Current V → Prop)
    [DecidablePred P]
    (bn : ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) × (↥G.edgeFinset → ℕ)) : ℝ :=
  (if sources G (ofEdgeFun G (bFull G S bn.1)) = ∅ then weight G β J (ofEdgeFun G (bFull G S bn.1)) else 0)
    * (if sources G (ofEdgeFun G bn.2) = ∅ then weight G β J (ofEdgeFun G bn.2) else 0)
    * (if P (fun e => ofEdgeFun G (bFull G S bn.1) e + ofEdgeFun G bn.2 e) then 1 else 0)


noncomputable def factorSummand (β : ℝ) (J : Sym2 V → ℝ) (S : Finset V) (A : Finset V)
    (a : {i : ↥G.edgeFinset // isIn G S i} → ℕ) : ℝ :=
  if sources G (ofEdgeFun G (aFull G S a)) = A then weight G β J (ofEdgeFun G (aFull G S a)) else 0


end Sharpness
end StatMech
