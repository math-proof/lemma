/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopVerticalWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part2
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

variable {T : EvenTorus}


theorem fkMedialDartIncoming_checkerArrows
    (T : EvenTorus) (d : FKMedialDart T) :
    fkMedialDartIncoming (fkMedialCheckerArrows T) d =
      fkMedialCheckerColor d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  cases side <;>
    simp [fkMedialDartIncoming, fkLoopWestIncoming,
      fkLoopEastIncoming, fkLoopSouthIncoming, fkLoopNorthIncoming,
      fkMedialCheckerArrows, fkMedialCheckerColor,
      fkMedialSideVertical]


theorem fkMedialCheckerArrows_compatible
    (T : EvenTorus) (pairing : FKMedialLoopPairing T) :
    ∀ v, fkLoopPairingCompatible (pairing v)
      (fkMedialCheckerArrows T) v := by
  intro v
  cases hp : pairing v <;>
    simp only [fkLoopPairingCompatible, Bool.false_eq_true,
      ite_false, ite_true]
  · constructor
    · change fkMedialDartIncoming (fkMedialCheckerArrows T) (v, .west) ≠
          fkMedialDartIncoming (fkMedialCheckerArrows T) (v, .north)
      rw [fkMedialDartIncoming_checkerArrows,
        fkMedialDartIncoming_checkerArrows]
      simpa [fkMedialLocalMate, hp] using
        (fkMedialCheckerColor_localMate_ne pairing (v, .west)).symm
    · change fkMedialDartIncoming (fkMedialCheckerArrows T) (v, .east) ≠
          fkMedialDartIncoming (fkMedialCheckerArrows T) (v, .south)
      rw [fkMedialDartIncoming_checkerArrows,
        fkMedialDartIncoming_checkerArrows]
      simpa [fkMedialLocalMate, hp] using
        (fkMedialCheckerColor_localMate_ne pairing (v, .east)).symm
  · constructor
    · change fkMedialDartIncoming (fkMedialCheckerArrows T) (v, .west) ≠
          fkMedialDartIncoming (fkMedialCheckerArrows T) (v, .south)
      rw [fkMedialDartIncoming_checkerArrows,
        fkMedialDartIncoming_checkerArrows]
      simpa [fkMedialLocalMate, hp] using
        (fkMedialCheckerColor_localMate_ne pairing (v, .west)).symm
    · change fkMedialDartIncoming (fkMedialCheckerArrows T) (v, .east) ≠
          fkMedialDartIncoming (fkMedialCheckerArrows T) (v, .north)
      rw [fkMedialDartIncoming_checkerArrows,
        fkMedialDartIncoming_checkerArrows]
      simpa [fkMedialLocalMate, hp] using
        (fkMedialCheckerColor_localMate_ne pairing (v, .east)).symm

theorem bool_eq_iff_eq_of_ne_ne
    {a b c d : Bool} (hab : a ≠ b) (hcd : c ≠ d) :
    (a = c ↔ b = d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all


theorem fkMedialDartIncoming_eq_checkerColor_iff_of_adj
    (pairing : FKMedialLoopPairing T) (arrows : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v)
    {d e : FKMedialDart T}
    (hde : (fkMedialLoopGraph T pairing).Adj d e) :
    (fkMedialDartIncoming arrows d = fkMedialCheckerColor d ↔
      fkMedialDartIncoming arrows e = fkMedialCheckerColor e) := by
  exact bool_eq_iff_eq_of_ne_ne
    (fkMedialLoopGraph_adj_incoming_ne pairing arrows hcompat hde)
    (fkMedialLoopGraph_adj_checkerColor_ne T pairing hde)


theorem fkMedialDartIncoming_eq_checkerColor_iff_of_reachable
    (pairing : FKMedialLoopPairing T) (arrows : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v)
    {d e : FKMedialDart T}
    (hde : (fkMedialLoopGraph T pairing).Reachable d e) :
    (fkMedialDartIncoming arrows d = fkMedialCheckerColor d ↔
      fkMedialDartIncoming arrows e = fkMedialCheckerColor e) := by
  obtain ⟨w⟩ := hde
  induction w with
  | nil => exact Iff.rfl
  | cons h w ih =>
      exact (fkMedialDartIncoming_eq_checkerColor_iff_of_adj
        pairing arrows hcompat h).trans ih

theorem fkOrientedVerticalSeamSign_eq_canonical_of_incoming_eq
    (T : EvenTorus) (arrows : SixVertexArrows T) (i : Fin T.width)
    (h : fkMedialDartIncoming arrows (fkMedialVerticalSeamDart T i) =
      fkMedialCheckerColor (fkMedialVerticalSeamDart T i)) :
    fkOrientedVerticalSeamSign T arrows i =
      fkMedialCanonicalVerticalSeamSign T i := by
  change (!arrows.vertical (i, svFinLast T.height_pos)) =
      fkMedialCheckerColor
        ((i, svFinLast T.height_pos), FKMedialSide.north) at h
  unfold fkOrientedVerticalSeamSign fkMedialCanonicalVerticalSeamSign
    fkMedialVerticalSeamDart
  cases ha : arrows.vertical (i, svFinLast T.height_pos) <;>
    cases hc : fkMedialCheckerColor
      ((i, svFinLast T.height_pos), FKMedialSide.north) <;>
    simp_all

theorem fkOrientedVerticalSeamSign_eq_neg_canonical_of_incoming_ne
    (T : EvenTorus) (arrows : SixVertexArrows T) (i : Fin T.width)
    (h : fkMedialDartIncoming arrows (fkMedialVerticalSeamDart T i) ≠
      fkMedialCheckerColor (fkMedialVerticalSeamDart T i)) :
    fkOrientedVerticalSeamSign T arrows i =
      -fkMedialCanonicalVerticalSeamSign T i := by
  change (!arrows.vertical (i, svFinLast T.height_pos)) ≠
      fkMedialCheckerColor
        ((i, svFinLast T.height_pos), FKMedialSide.north) at h
  unfold fkOrientedVerticalSeamSign fkMedialCanonicalVerticalSeamSign
    fkMedialVerticalSeamDart
  cases ha : arrows.vertical (i, svFinLast T.height_pos) <;>
    cases hc : fkMedialCheckerColor
      ((i, svFinLast T.height_pos), FKMedialSide.north) <;>
    simp_all


theorem fkOrientedMedialLoopVerticalFlux_eq_or_eq_neg
    (pairing : FKMedialLoopPairing T) (arrows : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v)
    (C : FKMedialLoop T pairing) :
    fkOrientedMedialLoopVerticalFlux pairing arrows C =
        fkMedialLoopCanonicalVerticalFlux pairing C ∨
      fkOrientedMedialLoopVerticalFlux pairing arrows C =
        -fkMedialLoopCanonicalVerticalFlux pairing C := by
  classical
  by_cases hmode : fkMedialDartIncoming arrows C.out =
      fkMedialCheckerColor C.out
  · left
    unfold fkOrientedMedialLoopVerticalFlux
      fkMedialLoopCanonicalVerticalFlux
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hC : (fkMedialLoopGraph T pairing).connectedComponentMk
        (fkMedialVerticalSeamDart T i) = C
    · rw [if_pos hC, if_pos hC]
      apply fkOrientedVerticalSeamSign_eq_canonical_of_incoming_eq
      have hreach : (fkMedialLoopGraph T pairing).Reachable C.out
          (fkMedialVerticalSeamDart T i) :=
        ConnectedComponent.exact (C.out_eq.trans hC.symm)
      exact (fkMedialDartIncoming_eq_checkerColor_iff_of_reachable
        pairing arrows hcompat hreach).1 hmode
    · rw [if_neg hC, if_neg hC]
  · right
    unfold fkOrientedMedialLoopVerticalFlux
      fkMedialLoopCanonicalVerticalFlux
    rw [← sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hC : (fkMedialLoopGraph T pairing).connectedComponentMk
        (fkMedialVerticalSeamDart T i) = C
    · rw [if_pos hC, if_pos hC]
      apply fkOrientedVerticalSeamSign_eq_neg_canonical_of_incoming_ne
      have hreach : (fkMedialLoopGraph T pairing).Reachable C.out
          (fkMedialVerticalSeamDart T i) :=
        ConnectedComponent.exact (C.out_eq.trans hC.symm)
      intro heq
      apply hmode
      exact (fkMedialDartIncoming_eq_checkerColor_iff_of_reachable
        pairing arrows hcompat hreach).2 heq
    · rw [if_neg hC, if_neg hC, neg_zero]


theorem fkOrientedMedialLoopVerticalFlux_natAbs
    (pairing : FKMedialLoopPairing T) (arrows : SixVertexArrows T)
    (hcompat : ∀ v, fkLoopPairingCompatible (pairing v) arrows v)
    (C : FKMedialLoop T pairing) :
    (fkOrientedMedialLoopVerticalFlux pairing arrows C).natAbs =
      (fkMedialLoopCanonicalVerticalFlux pairing C).natAbs := by
  rcases fkOrientedMedialLoopVerticalFlux_eq_or_eq_neg
      pairing arrows hcompat C with h | h
  · rw [h]
  · rw [h, Int.natAbs_neg]


theorem fkOrientedMedialLoopVerticalFlux_arrowsOfMode
    (pairing : FKMedialLoopPairing T)
    (mode : FKMedialLoop T pairing → Bool)
    (C : FKMedialLoop T pairing) :
    fkOrientedMedialLoopVerticalFlux pairing
        (FKMedialTurningFiber.arrowsOfMode pairing mode) C =
      if mode C then -fkMedialLoopCanonicalVerticalFlux pairing C
      else fkMedialLoopCanonicalVerticalFlux pairing C := by
  classical
  unfold fkOrientedMedialLoopVerticalFlux
    fkMedialLoopCanonicalVerticalFlux
  by_cases hm : mode C
  · rw [if_pos hm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hC : (fkMedialLoopGraph T pairing).connectedComponentMk
        (fkMedialVerticalSeamDart T i) = C
    · rw [if_pos hC, if_pos hC]
      apply fkOrientedVerticalSeamSign_eq_neg_canonical_of_incoming_ne
      rw [FKMedialTurningFiber.incoming_arrowsOfMode]
      unfold FKMedialTurningFiber.modeIncoming
      rw [hC, hm]
      simp
    · rw [if_neg hC, if_neg hC, neg_zero]
  · rw [if_neg hm]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hC : (fkMedialLoopGraph T pairing).connectedComponentMk
        (fkMedialVerticalSeamDart T i) = C
    · rw [if_pos hC, if_pos hC]
      apply fkOrientedVerticalSeamSign_eq_canonical_of_incoming_eq
      rw [FKMedialTurningFiber.incoming_arrowsOfMode]
      unfold FKMedialTurningFiber.modeIncoming
      rw [hC, if_neg hm]
    · rw [if_neg hC, if_neg hC]


end
end StatMech.FrontierD
