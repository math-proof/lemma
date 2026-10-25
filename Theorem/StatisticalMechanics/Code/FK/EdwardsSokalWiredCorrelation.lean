/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalWiredCorrelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part8
import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
import Def.StatisticalMechanics.Code.FK.EdwardsSokalWiredCorrelation
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


theorem sum_pottsBoundaryObservable (q : Nat) [NeZero q] (b : Fin q) :
    ∑ a : Fin q, pottsBoundaryObservable q b a = 0 := by
  classical
  unfold pottsBoundaryObservable
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

theorem sum_pinned_eq_filterQ
    {C : Type*} [Fintype C] [DecidableEq C] {q : Nat}
    (c0 : C) (b : Fin q) (F : (C → Fin q) → Real) :
    (∑ tau : {tau : C → Fin q // tau c0 = b}, F tau.1) =
      ∑ tau ∈ Finset.univ.filter (fun tau : C → Fin q => tau c0 = b), F tau :=
  (Finset.sum_subtype
    (Finset.univ.filter (fun tau : C → Fin q => tau c0 = b))
    (fun tau => by simp) F).symm

theorem colour_pottsBoundary_cancel
    {C : Type*} [Fintype C] [DecidableEq C]
    (q : Nat) [NeZero q] (b : Fin q) (c0 cx : C) (h : cx ≠ c0) :
    (∑ tau ∈ Finset.univ.filter (fun tau : C → Fin q => tau c0 = b),
      pottsBoundaryObservable q b (tau cx)) = 0 := by
  classical
  rw [← sum_pinned_eq_filterQ c0 b
    (fun tau => pottsBoundaryObservable q b (tau cx))]
  rw [← (pinnedFunEquiv c0 b).symm.sum_comp
    (fun tau : {tau : C → Fin q // tau c0 = b} =>
      pottsBoundaryObservable q b (tau.1 cx))]
  have hval : ∀ g : {c : C // c ≠ c0} → Fin q,
      (fun tau : {tau : C → Fin q // tau c0 = b} =>
        pottsBoundaryObservable q b (tau.1 cx))
          ((pinnedFunEquiv c0 b).symm g) =
        pottsBoundaryObservable q b (g ⟨cx, h⟩) := by
    intro g
    show pottsBoundaryObservable q b (((pinnedFunEquiv c0 b).symm g).1 cx) =
      pottsBoundaryObservable q b (g ⟨cx, h⟩)
    congr 1
    show (if hh : cx = c0 then b else g ⟨cx, hh⟩) = g ⟨cx, h⟩
    rw [dif_neg h]
  rw [Finset.sum_congr rfl (fun g _ => hval g)]
  rw [sum_eval_factor (⟨cx, h⟩ : {c : C // c ≠ c0})
    (pottsBoundaryObservable q b), sum_pottsBoundaryObservable, smul_zero]

theorem colour_pottsBoundary_const
    {C : Type*} [Fintype C] [DecidableEq C]
    (q : Nat) [NeZero q] (b : Fin q) (c0 cx : C) (h : cx = c0) :
    (∑ tau ∈ Finset.univ.filter (fun tau : C → Fin q => tau c0 = b),
      pottsBoundaryObservable q b (tau cx)) =
        ((q : Real) - 1) * (q : Real) ^ (Fintype.card C - 1) := by
  classical
  rw [← sum_pinned_eq_filterQ c0 b
    (fun tau => pottsBoundaryObservable q b (tau cx))]
  have hconst : ∀ tau : {tau : C → Fin q // tau c0 = b},
      pottsBoundaryObservable q b (tau.1 cx) = (q : Real) - 1 := by
    intro tau
    rw [h, tau.2]
    simp [pottsBoundaryObservable]
  rw [Finset.sum_congr rfl (fun tau _ => hconst tau), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, card_pinned c0 b]
  push_cast
  ring

theorem colour_pottsBoundary_sum
    {q : Nat} [NeZero q] (b : Fin q) (omega : ConfigSpace (Sym2 V))
    (v0 : V) (hv0 : bdry v0) (x : V) :
    (∑ sigma ∈ Finset.univ.filter
        (fun sigma : V → Fin q =>
          ConstOnWired G bdry omega sigma ∧ BoundaryFixed bdry b sigma),
      pottsBoundaryObservable q b (sigma x)) =
      if ConnToBdry G bdry omega x then
        ((q : Real) - 1) *
          (q : Real) ^ (Fintype.card (wiredSub G bdry omega).ConnectedComponent - 1)
      else 0 := by
  classical
  have hreindex :
      (∑ sigma ∈ Finset.univ.filter
          (fun sigma : V → Fin q =>
            ConstOnWired G bdry omega sigma ∧ BoundaryFixed bdry b sigma),
        pottsBoundaryObservable q b (sigma x)) =
      ∑ tau ∈ Finset.univ.filter
          (fun tau : (wiredSub G bdry omega).ConnectedComponent → Fin q =>
            tau ((wiredSub G bdry omega).connectedComponentMk v0) = b),
        pottsBoundaryObservable q b
          (tau ((wiredSub G bdry omega).connectedComponentMk x)) := by
    rw [Finset.sum_subtype (p := fun sigma : V → Fin q =>
          ConstOnWired G bdry omega sigma ∧ BoundaryFixed bdry b sigma)
      (Finset.univ.filter (fun sigma : V → Fin q =>
        ConstOnWired G bdry omega sigma ∧ BoundaryFixed bdry b sigma))
      (fun sigma => by simp)
      (fun sigma => pottsBoundaryObservable q b (sigma x))]
    rw [Finset.sum_subtype
      (p := fun tau : (wiredSub G bdry omega).ConnectedComponent → Fin q =>
        tau ((wiredSub G bdry omega).connectedComponentMk v0) = b)
      (Finset.univ.filter
        (fun tau : (wiredSub G bdry omega).ConnectedComponent → Fin q =>
          tau ((wiredSub G bdry omega).connectedComponentMk v0) = b))
      (fun tau => by simp)
      (fun tau => pottsBoundaryObservable q b
        (tau ((wiredSub G bdry omega).connectedComponentMk x)))]
    rw [← (wiredColourEquiv G bdry b omega v0 hv0).sum_comp
      (fun tau => pottsBoundaryObservable q b
        (tau.1 ((wiredSub G bdry omega).connectedComponentMk x)))]
    apply Finset.sum_congr rfl
    intro sigma _
    rw [wiredColourEquiv_apply_val]
  rw [hreindex]
  have hiff := connToBdry_iff_componentMk_eq G bdry v0 hv0 omega x
  by_cases h : (wiredSub G bdry omega).connectedComponentMk x =
      (wiredSub G bdry omega).connectedComponentMk v0
  · rw [if_pos (hiff.mpr h)]
    exact colour_pottsBoundary_const q b _ _ h
  · rw [if_neg (fun hc => h (hiff.mp hc))]
    exact colour_pottsBoundary_cancel q b _ _ h

theorem esWeightWired_pottsBoundary_sum
    {q : Nat} [NeZero q] (b : Fin q) (p : Real)
    (omega : ConfigSpace (Sym2 V)) (v0 : V) (hv0 : bdry v0) (x : V) :
    (∑ sigma : V → Fin q,
      esWeightWired G bdry b p sigma omega *
        pottsBoundaryObservable q b (sigma x)) =
      edgeProduct G p omega *
        (if ConnToBdry G bdry omega x then
          ((q : Real) - 1) *
            (q : Real) ^ (numClustersBC G (boundaryCliqueGraph bdry) omega - 1)
        else 0) := by
  classical
  have hterm : ∀ sigma : V → Fin q,
      esWeightWired G bdry b p sigma omega *
          pottsBoundaryObservable q b (sigma x) =
        (if ConstOnOpen G omega sigma ∧ BoundaryFixed bdry b sigma then
          edgeProduct G p omega else 0) *
            pottsBoundaryObservable q b (sigma x) := by
    intro sigma
    unfold esWeightWired
    rw [esWeight_eq_of_compatible]
    simp only [compatible_iff_constOnOpen]
    by_cases hb : BoundaryFixed bdry b sigma <;>
      by_cases hc : ConstOnOpen G omega sigma <;> simp [hb, hc]
  rw [Finset.sum_congr rfl (fun sigma _ => hterm sigma)]
  rw [Finset.sum_congr rfl (fun sigma _ => by rw [ite_mul, zero_mul])]
  rw [← Finset.sum_filter]
  rw [Finset.sum_congr (Finset.filter_congr (fun sigma _ => by
    rw [constOnOpen_boundaryFixed_iff])) (fun sigma _ => rfl)]
  rw [← Finset.mul_sum, colour_pottsBoundary_sum G bdry b omega v0 hv0 x]
  rw [numClustersBC_eq_card_wiredSub]


end IsingFK
end StatMech
