/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedEdgeLumping.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Def.StatisticalMechanics.Code.FK.IndexedEdgeLumping
open Finset


namespace StatMech.FK

noncomputable section

variable {E A : Type*} [Fintype E] [DecidableEq E]
  [Fintype A] [DecidableEq A]


theorem indexedFiberWeight_sum (p : Real) (f : E → A) (a : A) :
    ∑ eta : {e : E // f e = a} → Bool, indexedFiberWeight p eta = 1 := by
  unfold indexedFiberWeight
  rw [← Fintype.prod_sum (fun (_ : {e : E // f e = a}) (b : Bool) =>
    if b then p else 1 - p)]
  simp

theorem indexedFiberWeight_allFalse (p : Real) (f : E → A) (a : A) :
    indexedFiberWeight p (fun _ : {e : E // f e = a} => false) =
      (1 - p) ^ (indexedBundle f a).card := by
  unfold indexedFiberWeight indexedBundle
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_subtype]
  rfl

theorem indexedFiberMass_false (p : Real) (f : E → A) (a : A) :
    ∑ eta : {e : E // f e = a} → Bool,
      (if indexedFiberOr f a eta = false then indexedFiberWeight p eta else 0) =
        1 - indexedEffectiveParam f p a := by
  have hsingle : ∀ eta : {e : E // f e = a} → Bool,
      indexedFiberOr f a eta = false →
        eta = fun _ : {e : E // f e = a} => false := by
    intro eta heta
    funext e
    apply Bool.eq_false_iff.mpr
    intro he
    have hnot : ¬ ∃ u : {e : E // f e = a}, eta u = true := by
      simpa [indexedFiberOr] using heta
    exact hnot ⟨e, he⟩
  rw [Finset.sum_eq_single
    (fun _ : {e : E // f e = a} => false)]
  · rw [if_pos]
    · rw [indexedFiberWeight_allFalse]
      simp [indexedEffectiveParam]
    · simp [indexedFiberOr]
  · intro eta _ hne
    have hor : indexedFiberOr f a eta = true := by
      cases h : indexedFiberOr f a eta
      · exact absurd (hsingle eta h) hne
      · rfl
    simp [hor]
  · simp

theorem indexedFiberMass (p : Real) (f : E → A) (a : A) (b : Bool) :
    ∑ eta : {e : E // f e = a} → Bool,
      (if indexedFiberOr f a eta = b then indexedFiberWeight p eta else 0) =
        if b then indexedEffectiveParam f p a else
          1 - indexedEffectiveParam f p a := by
  cases b
  · simpa using indexedFiberMass_false p f a
  · have hsplit :
        (∑ eta : {e : E // f e = a} → Bool,
          (if indexedFiberOr f a eta = true then indexedFiberWeight p eta else 0)) +
        (∑ eta : {e : E // f e = a} → Bool,
          (if indexedFiberOr f a eta = false then indexedFiberWeight p eta else 0)) = 1 := by
      rw [← Finset.sum_add_distrib]
      calc
        ∑ eta : {e : E // f e = a} → Bool,
            ((if indexedFiberOr f a eta = true then indexedFiberWeight p eta else 0) +
              if indexedFiberOr f a eta = false then indexedFiberWeight p eta else 0) =
            ∑ eta, indexedFiberWeight p eta := by
              apply Finset.sum_congr rfl
              intro eta _
              cases indexedFiberOr f a eta <;> simp
        _ = 1 := indexedFiberWeight_sum p f a
    have hfalse := indexedFiberMass_false p f a
    simp only [if_true]
    linarith

end
end StatMech.FK
