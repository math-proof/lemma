/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CardyDiscreteHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.CardyDiscreteHolo.Part6


namespace StatMech.Universality

open Complex


theorem cardyDiscrete_CR (L : CardyLocalConfig) (v d : ℂ)
    (hpq : (triFace v d 0 + triFace v d 1) / 2 ≠ (triFace v d 1 + triFace v d 2) / 2)
    (hpr : (triFace v d 0 + triFace v d 1) / 2 ≠ (triFace v d 2 + triFace v d 0) / 2)
    (hqr : (triFace v d 1 + triFace v d 2) / 2 ≠ (triFace v d 2 + triFace v d 0) / 2) :
    triContour (cardyObservable L v d) (triFace v d) = 0 := by
  rw [triContour_eq_cardyS]
  
  have h0 : cardyObservable L v d ((triFace v d 0 + triFace v d 1) / 2) = L.crossingFun 0 := by
    unfold cardyObservable; rw [if_pos rfl]
  have h1 : cardyObservable L v d ((triFace v d 1 + triFace v d 2) / 2) = L.crossingFun 1 := by
    unfold cardyObservable
    rw [if_neg hpq.symm, if_pos rfl]
  have h2 : cardyObservable L v d ((triFace v d 2 + triFace v d 0) / 2) = L.crossingFun 2 := by
    unfold cardyObservable
    rw [if_neg hpr.symm, if_neg hqr.symm, if_pos rfl]
  rw [h0, h1, h2, L.crossingCombination_zero, mul_zero]


theorem cardyDiscrete_CR_closedPath (L : CardyLocalConfig)
    {ι : Type*} (faces : Finset ι) (tri : ι → ℂ × ℂ)
    (hdist : ∀ i ∈ faces,
      (triFace (tri i).1 (tri i).2 0 + triFace (tri i).1 (tri i).2 1) / 2
          ≠ (triFace (tri i).1 (tri i).2 1 + triFace (tri i).1 (tri i).2 2) / 2 ∧
      (triFace (tri i).1 (tri i).2 0 + triFace (tri i).1 (tri i).2 1) / 2
          ≠ (triFace (tri i).1 (tri i).2 2 + triFace (tri i).1 (tri i).2 0) / 2 ∧
      (triFace (tri i).1 (tri i).2 1 + triFace (tri i).1 (tri i).2 2) / 2
          ≠ (triFace (tri i).1 (tri i).2 2 + triFace (tri i).1 (tri i).2 0) / 2) :
    ∑ i ∈ faces,
      triContour (cardyObservable L (tri i).1 (tri i).2) (triFace (tri i).1 (tri i).2) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  obtain ⟨hpq, hpr, hqr⟩ := hdist i hi
  exact cardyDiscrete_CR L (tri i).1 (tri i).2 hpq hpr hqr

end StatMech.Universality
