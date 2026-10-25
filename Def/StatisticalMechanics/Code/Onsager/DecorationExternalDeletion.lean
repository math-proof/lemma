/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationExternalDeletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSupport


namespace StatMech.Onsager

open Matrix BigOperators

noncomputable def ons_decPhaseBucketE
    (L : ℕ) [NeZero L] (decWeight : ons_DecEdge L → ℂ)
    (a b : Fin 2) (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ loop ∈ Finset.univ.filter
      (fun loop : Fin (n + 1) → ons_Dart L =>
        (∃ i, loop i = e) ∧
          ¬ ∃ j, loop j = ons_dartRev L e),
    ons_loopWeight
      (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)) loop

noncomputable def ons_decPhaseBucketN
    (L : ℕ) [NeZero L] (decWeight : ons_DecEdge L → ℂ)
    (a b : Fin 2) (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ loop ∈ Finset.univ.filter
      (fun loop : Fin (n + 1) → ons_Dart L =>
        ¬ (∃ i, loop i = e) ∧
          ¬ ∃ j, loop j = ons_dartRev L e),
    ons_loopWeight
      (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)) loop

noncomputable def ons_decMaskPhaseBucketE
    (L : ℕ) [NeZero L] (decWeight : ons_DecEdge L → ℂ)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ loop ∈ Finset.univ.filter
      (fun loop : Fin (n + 1) → ons_Dart L =>
        (∃ i, loop i = e) ∧
          ¬ ∃ j, loop j = ons_dartRev L e),
    ons_loopWeight
      (ons_maskMatrix forbidden
        (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))) loop

noncomputable def ons_decMaskPhaseBucketN
    (L : ℕ) [NeZero L] (decWeight : ons_DecEdge L → ℂ)
    (a b : Fin 2) (forbidden : Finset (ons_Dart L))
    (e : ons_Dart L) (n : ℕ) : ℂ :=
  ∑ loop ∈ Finset.univ.filter
      (fun loop : Fin (n + 1) → ons_Dart L =>
        ¬ (∃ i, loop i = e) ∧
          ¬ ∃ j, loop j = ons_dartRev L e),
    ons_loopWeight
      (ons_maskMatrix forbidden
      (ons_KWmatDecorationWeightedPhase L decWeight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))) loop

def ons_scaleDecEdgeWeight
    {L : ℕ} (decWeight : ons_DecEdge L → ℂ)
    (edge : ons_DecEdge L) (t : ℂ) : ons_DecEdge L → ℂ :=
  fun f => if f = edge then t * decWeight f else decWeight f

end StatMech.Onsager
