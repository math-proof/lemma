/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFourReplicaCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option maxHeartbeats 8000000


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


def grahamQuadEquivSigma {E : Type*} :
    ((E -> Nat) × (E -> Nat) × (E -> Nat) × (E -> Nat)) ≃
      Sigma (fun total : E -> Nat =>
        {pqr : (E -> Nat) × (E -> Nat) × (E -> Nat) //
          ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e}) where
  toFun z :=
    ⟨fun e => z.1 e + z.2.1 e + z.2.2.1 e + z.2.2.2 e,
      ⟨(z.1, z.2.1, z.2.2.1), fun e => by simp only; omega⟩⟩
  invFun s :=
    (s.2.1.1, s.2.1.2.1, s.2.1.2.2,
      fun e => s.1 e - s.2.1.1 e - s.2.1.2.1 e - s.2.1.2.2 e)
  left_inv := by
    rintro ⟨a, b, c, d⟩
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
    funext e
    simp only
    omega
  right_inv := by
    rintro ⟨total, ⟨⟨a, b, c⟩, habc⟩⟩
    have htotal :
        (fun e => a e + b e + c e +
          (total e - a e - b e - c e)) = total := by
      funext e
      have h := habc e
      dsimp at h ⊢
      omega
    exact Sigma.subtype_ext htotal (by simp only)


def grahamPairPairEquivSigma {E : Type*} :
    (((E -> Nat) × (E -> Nat)) × ((E -> Nat) × (E -> Nat))) ≃
      Sigma (fun total : E -> Nat =>
        {pqr : (E -> Nat) × (E -> Nat) × (E -> Nat) //
          ∀ e, pqr.1 e + pqr.2.1 e + pqr.2.2 e ≤ total e}) :=
  ({ toFun := fun z => (z.1.1, z.1.2, z.2.1, z.2.2)
     invFun := fun z => ((z.1, z.2.1), (z.2.2.1, z.2.2.2))
     left_inv := by rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
     right_inv := by rintro ⟨a, b, c, d⟩; rfl } :
    (((E -> Nat) × (E -> Nat)) × ((E -> Nat) × (E -> Nat))) ≃
      ((E -> Nat) × (E -> Nat) × (E -> Nat) × (E -> Nat))).trans
    grahamQuadEquivSigma


end StatMech.FrontierA
