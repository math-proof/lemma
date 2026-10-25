/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFourReplicaCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamWeightedFourReplicaCore
open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option maxHeartbeats 8000000


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable instance grahamFintypeQuadLe
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (total : G.edgeFinset -> Nat) :
    Fintype {pqr : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) ×
        (G.edgeFinset -> Nat) //
      ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e} := by
  let embed := fun s : {pqr : (G.edgeFinset -> Nat) ×
      (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) //
      ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e} =>
    (fun e => (⟨s.1.1 e, by have := s.2 e; omega⟩ : Fin (total e + 1)),
      fun e => (⟨s.1.2.1 e, by have := s.2 e; omega⟩ : Fin (total e + 1)),
      fun e => (⟨s.1.2.2 e, by have := s.2 e; omega⟩ : Fin (total e + 1)))
  letI : Finite {pqr : (G.edgeFinset -> Nat) ×
      (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) //
      ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e} :=
    Finite.of_injective embed (by
      intro a b h
      apply Subtype.ext
      apply Prod.ext
      · funext e
        have he := congrFun (congrArg Prod.fst h) e
        simpa [embed] using he
      · apply Prod.ext
        · funext e
          have he := congrFun (congrArg (fun z => z.2.1) h) e
          simpa [embed] using he
        · funext e
          have he := congrFun (congrArg (fun z => z.2.2) h) e
          simpa [embed] using he)
  exact Fintype.ofFinite _


end StatMech.FrontierA
