/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFourReplicaCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Instance.StatisticalMechanics.Code.FrontierA.GrahamWeightedFourReplicaCore
open Finset SimpleGraph
open scoped BigOperators
open Classical

set_option maxHeartbeats 8000000


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem grahamOfEdgeFun_add4
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c d : G.edgeFinset -> Nat) :
    (fun e => ofEdgeFun G a e + ofEdgeFun G b e +
      ofEdgeFun G c e + ofEdgeFun G d e) =
      ofEdgeFun G (fun e => a e + b e + c e + d e) := by
  ext e
  unfold ofEdgeFun
  by_cases he : e ∈ G.edgeFinset <;> simp [he]


theorem grahamWeight_mul4_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (a b c d : Current V) :
    weight G beta J a * weight G beta J b *
        weight G beta J c * weight G beta J d =
      (∏ e ∈ G.edgeFinset,
        (Nat.choose (a e + b e + c e + d e) (a e) : Real) *
          (Nat.choose (b e + c e + d e) (b e) : Real) *
          (Nat.choose (c e + d e) (c e) : Real)) *
        weight G beta J (fun e => a e + b e + c e + d e) := by
  have hcd := weight_mul_eq G beta J c d
  have hbcd := weight_mul_eq G beta J b (fun e => c e + d e)
  have habcd := weight_mul_eq G beta J a
    (fun e => b e + c e + d e)
  calc
    weight G beta J a * weight G beta J b *
        weight G beta J c * weight G beta J d =
      weight G beta J a *
        (weight G beta J b * (weight G beta J c * weight G beta J d)) := by
          ring
    _ = weight G beta J a * (weight G beta J b *
        ((∏ e ∈ G.edgeFinset,
          (Nat.choose (c e + d e) (c e) : Real)) *
            weight G beta J (fun e => c e + d e))) := by rw [hcd]
    _ = (∏ e ∈ G.edgeFinset,
          (Nat.choose (c e + d e) (c e) : Real)) *
        (weight G beta J a *
          (weight G beta J b * weight G beta J (fun e => c e + d e))) := by
            ring
    _ = (∏ e ∈ G.edgeFinset,
          (Nat.choose (c e + d e) (c e) : Real)) *
        (weight G beta J a *
          ((∏ e ∈ G.edgeFinset,
            (Nat.choose (b e + (c e + d e)) (b e) : Real)) *
              weight G beta J (fun e => b e + (c e + d e)))) := by
                rw [hbcd]
    _ = (∏ e ∈ G.edgeFinset,
          (Nat.choose (c e + d e) (c e) : Real)) *
        (∏ e ∈ G.edgeFinset,
          (Nat.choose (b e + c e + d e) (b e) : Real)) *
        (weight G beta J a *
          weight G beta J (fun e => b e + c e + d e)) := by ring
    _ = (∏ e ∈ G.edgeFinset,
          (Nat.choose (c e + d e) (c e) : Real)) *
        (∏ e ∈ G.edgeFinset,
          (Nat.choose (b e + c e + d e) (b e) : Real)) *
        ((∏ e ∈ G.edgeFinset,
          (Nat.choose (a e + (b e + c e + d e)) (a e) : Real)) *
            weight G beta J (fun e => a e + (b e + c e + d e))) := by
              rw [habcd]
    _ = _ := by
      have hprod :
          (∏ e ∈ G.edgeFinset,
              (Nat.choose (c e + d e) (c e) : Real)) *
            (∏ e ∈ G.edgeFinset,
              (Nat.choose (b e + c e + d e) (b e) : Real)) *
            (∏ e ∈ G.edgeFinset,
              (Nat.choose (a e + (b e + c e + d e)) (a e) : Real)) =
          ∏ e ∈ G.edgeFinset,
            (Nat.choose (a e + b e + c e + d e) (a e) : Real) *
              (Nat.choose (b e + c e + d e) (b e) : Real) *
              (Nat.choose (c e + d e) (c e) : Real) := by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro e he
        ring
      rw [show (fun e => a e + (b e + c e + d e)) =
          (fun e => a e + b e + c e + d e) by
        funext e; omega]
      calc
        ((∏ e ∈ G.edgeFinset,
              (Nat.choose (c e + d e) (c e) : Real)) *
            (∏ e ∈ G.edgeFinset,
              (Nat.choose (b e + c e + d e) (b e) : Real))) *
            ((∏ e ∈ G.edgeFinset,
              (Nat.choose (a e + (b e + c e + d e)) (a e) : Real)) *
              weight G beta J (fun e => a e + b e + c e + d e)) =
          ((∏ e ∈ G.edgeFinset,
              (Nat.choose (c e + d e) (c e) : Real)) *
            (∏ e ∈ G.edgeFinset,
              (Nat.choose (b e + c e + d e) (b e) : Real)) *
            (∏ e ∈ G.edgeFinset,
              (Nat.choose (a e + (b e + c e + d e)) (a e) : Real))) *
              weight G beta J (fun e => a e + b e + c e + d e) := by ring
        _ = _ := by rw [hprod]


theorem grahamWeight_split4_eq_binom
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    (total a b c : G.edgeFinset -> Nat)
    (habc : ∀ e, a e + b e + c e ≤ total e) :
    weight G beta J (ofEdgeFun G a) *
        weight G beta J (ofEdgeFun G b) *
        weight G beta J (ofEdgeFun G c) *
        weight G beta J
          (ofEdgeFun G (fun e => total e - a e - b e - c e)) =
      (∏ e : G.edgeFinset,
        (Nat.choose (total e) (a e) : Real) *
          (Nat.choose (total e - a e) (b e) : Real) *
          (Nat.choose (total e - a e - b e) (c e) : Real)) *
        weight G beta J (ofEdgeFun G total) := by
  let d : G.edgeFinset -> Nat :=
    fun e => total e - a e - b e - c e
  have hsplit : ofEdgeFun G total =
      fun e => ofEdgeFun G a e + ofEdgeFun G b e +
        ofEdgeFun G c e + ofEdgeFun G d e := by
    rw [grahamOfEdgeFun_add4]
    congr 1
    funext e
    dsimp [d]
    have h := habc e
    omega
  rw [grahamWeight_mul4_eq G beta J]
  apply congrArg₂ (· * ·)
  · rw [← Finset.prod_attach G.edgeFinset]
    apply Finset.prod_congr rfl
    intro e he
    have h := habc e
    simp only [ofEdgeFun, dif_pos e.2]
    dsimp [d]
    have h0 : a e + b e + c e +
        (total e - a e - b e - c e) = total e := by omega
    have h1 : b e + c e + (total e - a e - b e - c e) =
        total e - a e := by omega
    have h2 : c e + (total e - a e - b e - c e) =
        total e - a e - b e := by omega
    rw [h0, h1, h2]
  · dsimp [d] at hsplit
    exact congrArg (weight G beta J) hsplit.symm

end StatMech.FrontierA
