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
import Instance.StatisticalMechanics.Code.Sharpness.ClaimIsingFull
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def aFull (S : Finset V) (a : {i : ↥G.edgeFinset // isIn G S i} → ℕ) :
    ↥G.edgeFinset → ℕ := fun i => if h : isIn G S i then a ⟨i, h⟩ else 0


noncomputable def bFull (S : Finset V) (b : {i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ) :
    ↥G.edgeFinset → ℕ := fun i => if h : isIn G S i then 0 else b ⟨i, h⟩


noncomputable def reEdge (S : Finset V)
    (ab : ({i : ↥G.edgeFinset // isIn G S i} → ℕ) × ({i : ↥G.edgeFinset // ¬ isIn G S i} → ℕ)) :
    ↥G.edgeFinset → ℕ := (Equiv.piEquivPiSubtypeProd (isIn G S) (fun _ => ℕ)).symm ab

end Sharpness
end StatMech
