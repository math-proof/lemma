/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalExternal.Part3
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalFirstReturn.Part12


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decFormalFirstReturnCoeff_eq_sum_boundedAtoms
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) :
    ons_decFormalFirstReturnCoeff L a b d m =
      ∑ atom : ons_DecFirstReturnAtomBounded L d
          (ons_finsuppTotalDegree m),
        if ons_decBoundedAtomExponent atom = m then
          ons_decBoundedAtomWeight L a b atom
        else 0 := by
  classical
  unfold ons_decFormalFirstReturnCoeff
  rw [Fintype.sum_sigma]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro rf hrf
  change (∑ loop : Fin (rf.val + 1) → ons_Dart L,
      if ons_decIsFirstReturnLoop d loop ∧
          ons_decLoopExponent L loop = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop
      else 0) =
    ∑ loop : {loop : Fin (rf.val + 1) → ons_Dart L //
        ons_decIsFirstReturnLoop d loop},
      if ons_decLoopExponent L loop.1 = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop.1
      else 0
  rw [← Finset.sum_subtype
    (s := Finset.univ.filter (ons_decIsFirstReturnLoop d))
    (by simp)
    (fun loop : Fin (rf.val + 1) → ons_Dart L ↦
      if ons_decLoopExponent L loop = m then
        ons_decLoopScalar L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b) loop
      else 0)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro loop hloop
  by_cases hfirst : ons_decIsFirstReturnLoop d loop
  · simp [hfirst]
  · simp [hfirst]

end StatMech.Onsager
