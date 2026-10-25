/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MultiReplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsing.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Def.StatisticalMechanics.Code.Sharpness.MultiReplica
open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable instance instFintypeTripleLe (m : ↥G.edgeFinset → ℕ) :
    Fintype {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e} := by
  classical
  have hfin : Finite {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e} := by
    apply Finite.of_injective
      (f := fun s : {pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) // ∀ e, pq.1 e + pq.2 e ≤ m e} =>
        (fun e => (⟨s.1.1 e, by have := s.2 e; omega⟩ : Fin (m e + 1)),
         fun e => (⟨s.1.2 e, by have := s.2 e; omega⟩ : Fin (m e + 1))))
    intro a b h
    apply Subtype.ext
    apply Prod.ext
    · funext e
      have h2 := congrFun (congrArg Prod.fst h) e
      simpa using h2
    · funext e
      have h2 := congrFun (congrArg Prod.snd h) e
      simpa using h2
  exact Fintype.ofFinite _


end Sharpness
end StatMech
