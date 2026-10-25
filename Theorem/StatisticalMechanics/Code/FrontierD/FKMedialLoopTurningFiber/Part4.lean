/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurningFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Def.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part4
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}

namespace FKMedialTurningFiber

theorem turnSign_not (p b : Bool) :
    turnSign p (!b) = -turnSign p b := by
  cases p <;> cases b <;> rfl

theorem componentTurn_arrowsOfMode
    (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing → Bool) (C : FKMedialLoop T pairing) :
    componentTurn pairing (arrowsOfMode pairing mode) C =
      if mode C then -canonicalComponentTurn pairing C
      else canonicalComponentTurn pairing C := by
  classical
  have hpoint (v : T.Vertex) :
      ((if (fkMedialLoopGraph T pairing).connectedComponentMk (v, .west) = C
          then turnSign (pairing v)
            (fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .west))
          else 0) +
        (if (fkMedialLoopGraph T pairing).connectedComponentMk (v, .east) = C
          then turnSign (pairing v)
            (fkMedialDartIncoming (arrowsOfMode pairing mode) (v, .east))
          else 0)) =
      if mode C then
        -((if (fkMedialLoopGraph T pairing).connectedComponentMk (v, .west) = C
            then turnSign (pairing v)
              (fkMedialDartIncoming
                (arrowsOfMode pairing fun _ => false) (v, .west))
            else 0) +
          (if (fkMedialLoopGraph T pairing).connectedComponentMk (v, .east) = C
            then turnSign (pairing v)
              (fkMedialDartIncoming
                (arrowsOfMode pairing fun _ => false) (v, .east))
            else 0))
      else
        ((if (fkMedialLoopGraph T pairing).connectedComponentMk (v, .west) = C
            then turnSign (pairing v)
              (fkMedialDartIncoming
                (arrowsOfMode pairing fun _ => false) (v, .west))
            else 0) +
          (if (fkMedialLoopGraph T pairing).connectedComponentMk (v, .east) = C
            then turnSign (pairing v)
              (fkMedialDartIncoming
                (arrowsOfMode pairing fun _ => false) (v, .east))
            else 0)) := by
    by_cases hw : (fkMedialLoopGraph T pairing).connectedComponentMk
        (v, .west) = C <;>
      by_cases he : (fkMedialLoopGraph T pairing).connectedComponentMk
        (v, .east) = C
    all_goals rw [incoming_arrowsOfMode, incoming_arrowsOfMode,
      incoming_arrowsOfMode, incoming_arrowsOfMode]
    all_goals unfold modeIncoming
    all_goals simp only [hw, he, if_true, if_false]
    all_goals cases hm : mode C <;>
      cases hp : pairing v <;>
      cases hwc : fkMedialCheckerColor (v, .west) <;>
      cases hec : fkMedialCheckerColor (v, .east) <;>
      simp [turnSign]
  by_cases hm : mode C
  · rw [if_pos hm]
    unfold canonicalComponentTurn componentTurn
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    simpa [hm] using hpoint v
  · rw [if_neg hm]
    unfold canonicalComponentTurn componentTurn
    apply Finset.sum_congr rfl
    intro v hv
    simpa [hm] using hpoint v

theorem sum_componentTurn_eq_vertexTurn
    (pairing : FKMedialLoopPairing T) (a : SixVertexArrows T) :
    (∑ C : FKMedialLoop T pairing, componentTurn pairing a C) =
      ∑ v : T.Vertex, vertexTurn (pairing v) a v := by
  classical
  unfold componentTurn vertexTurn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp [Finset.sum_add_distrib, fkMedialDartIncoming]

theorem orientedLoopWeight_eq_exp_sum_componentTurn
    (lam : Real) (pairing : FKMedialLoopPairing T)
    (a : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) a v) :
    fkOrientedLoopPairingWeight lam pairing a =
      Real.exp ((lam / 4) *
        ∑ C : FKMedialLoop T pairing, componentTurn pairing a C) := by
  unfold fkOrientedLoopPairingWeight
  simp_rw [local_eq lam _ a _ (hcompat _)]
  rw [← Real.exp_sum]
  rw [sum_componentTurn_eq_vertexTurn]
  congr 1
  push_cast
  simpa using (Finset.mul_sum (s := Finset.univ)
    (f := fun v : T.Vertex => (vertexTurn (pairing v) a v : Real))
    (lam / 4)).symm

theorem orientedLoopWeight_arrowsOfMode
    (lam : Real) (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing → Bool) :
    fkOrientedLoopPairingWeight lam pairing (arrowsOfMode pairing mode) =
      ∏ C : FKMedialLoop T pairing,
        if mode C then Real.exp (-(lam / 4) * canonicalComponentTurn pairing C)
        else Real.exp ((lam / 4) * canonicalComponentTurn pairing C) := by
  rw [orientedLoopWeight_eq_exp_sum_componentTurn lam pairing _
    (compatible_arrowsOfMode pairing mode)]
  rw [show Real.exp ((lam / 4) *
        ∑ C : FKMedialLoop T pairing,
          componentTurn pairing (arrowsOfMode pairing mode) C) =
      ∏ C : FKMedialLoop T pairing,
        Real.exp ((lam / 4) *
          componentTurn pairing (arrowsOfMode pairing mode) C) by
    rw [← Real.exp_sum]
    congr 1
    push_cast
    simpa using (Finset.mul_sum (s := Finset.univ)
      (f := fun C : FKMedialLoop T pairing =>
        (componentTurn pairing (arrowsOfMode pairing mode) C : Real))
      (lam / 4))]
  apply Finset.prod_congr rfl
  intro C hC
  rw [componentTurn_arrowsOfMode]
  split <;> congr 1 <;> push_cast <;> ring

theorem sum_orientedLoopWeight_eq_sum_modes
    (lam : Real) (pairing : FKMedialLoopPairing T) :
    (∑ a : SixVertexArrows T,
        fkOrientedLoopPairingWeight lam pairing a) =
      ∑ mode : (FKMedialLoop T pairing → Bool),
        fkOrientedLoopPairingWeight lam pairing
          (arrowsOfMode pairing mode) := by
  classical
  let p : SixVertexArrows T → Prop := fun a =>
    ∀ v, fkLoopPairingCompatible (pairing v) a v
  let f : SixVertexArrows T → Real := fun a =>
    fkOrientedLoopPairingWeight lam pairing a
  have hzero (a : SixVertexArrows T) (ha : ¬p a) : f a = 0 := by
    change ¬∀ v, fkLoopPairingCompatible (pairing v) a v at ha
    push Not at ha
    obtain ⟨v, hv⟩ := ha
    unfold f fkOrientedLoopPairingWeight
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp [fkOrientedLoopLocalWeight, hv]
  calc
    (∑ a : SixVertexArrows T, f a) =
        ∑ a : SixVertexArrows T, if p a then f a else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hpa : p a
      · rw [if_pos hpa]
      · rw [if_neg hpa, hzero a hpa]
    _ = (∑ a ∈ (Finset.univ.filter p), f a) := by
      symm
      simpa using Finset.sum_filter p f
    _ = ∑ a : {a : SixVertexArrows T // p a}, f a.1 := by
      symm
      simpa using Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset (SixVertexArrows T))) (p := p) f
    _ = ∑ mode : (FKMedialLoop T pairing → Bool),
          f (arrowsOfMode pairing mode) := by
      symm
      apply Fintype.sum_equiv (modeEquivCompatibleArrows pairing)
      intro mode
      rfl

theorem sum_orientedLoopWeight_eq_turningProduct
    (lam : Real) (pairing : FKMedialLoopPairing T) :
    (∑ a : SixVertexArrows T,
        fkOrientedLoopPairingWeight lam pairing a) =
      ∏ C : FKMedialLoop T pairing,
        (Real.exp ((lam / 4) * canonicalComponentTurn pairing C) +
          Real.exp (-(lam / 4) * canonicalComponentTurn pairing C)) := by
  rw [sum_orientedLoopWeight_eq_sum_modes]
  simp_rw [orientedLoopWeight_arrowsOfMode]
  let g : FKMedialLoop T pairing → Bool → Real := fun C b =>
    if b then Real.exp (-(lam / 4) * canonicalComponentTurn pairing C)
    else Real.exp ((lam / 4) * canonicalComponentTurn pairing C)
  change (∑ x : (FKMedialLoop T pairing → Bool), ∏ C, g C (x C)) = _
  rw [← Fintype.prod_sum]
  apply Finset.prod_congr rfl
  intro C hC
  simp [g, add_comm]


theorem orientationFactor_eq_two_of_turn_eq_zero
    (lam : Real) (pairing : FKMedialLoopPairing T)
    (C : FKMedialLoop T pairing)
    (hC : canonicalComponentTurn pairing C = 0) :
    Real.exp ((lam / 4) * canonicalComponentTurn pairing C) +
        Real.exp (-(lam / 4) * canonicalComponentTurn pairing C) = 2 := by
  rw [hC]
  norm_num


theorem orientationFactor_eq_exp_add_exp_neg_of_turn_eq_four_or_neg_four
    (lam : Real) (pairing : FKMedialLoopPairing T)
    (C : FKMedialLoop T pairing)
    (hC : canonicalComponentTurn pairing C = 4 ∨
      canonicalComponentTurn pairing C = -4) :
      Real.exp ((lam / 4) * canonicalComponentTurn pairing C) +
        Real.exp (-(lam / 4) * canonicalComponentTurn pairing C) =
      Real.exp lam + Real.exp (-lam) := by
  rcases hC with hC | hC
  · rw [hC]
    congr 1 <;> ring
  · rw [hC, add_comm]
    congr 1 <;> ring

end FKMedialTurningFiber
end
end StatMech.FrontierD
