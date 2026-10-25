/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Onsager.ShermanSplit.Part5


namespace StatMech.Onsager

open Matrix BigOperators Finset Complex

set_option linter.unusedSectionVars false

section Split

variable {E : Type*} [DecidableEq E]


theorem ons_firstReturnFactors_spec (e : E) (w : List E)
    (hhead : w.head? = some e) (hlast : w.getLast? = some e) :
    ons_firstReturnSplit e w = ons_firstReturnFactors e w ++ [[e]] ∧
    (∀ s ∈ ons_firstReturnFactors e w, ons_isFirstReturnSegment e s) ∧
    ons_glue e (ons_firstReturnFactors e w) = w := by
  obtain ⟨ss, hsplit, hvalid⟩ := ons_firstReturnSplit_closed e w hhead hlast
  have hfactors : ons_firstReturnFactors e w = ss := by
    unfold ons_firstReturnFactors
    rw [hsplit]
    simp
  rw [hfactors]
  refine ⟨hsplit, hvalid, ?_⟩
  rw [← ons_glue_append_terminal]
  rw [← hsplit]
  exact ons_glue_firstReturnSplit e w hlast


theorem ons_edgeWeight_firstReturnSplit (Λ : Matrix E E ℂ) (e : E) (w : List E) :
    ((ons_firstReturnSplit e w).map (ons_edgeWeight Λ)).prod = ons_edgeWeight Λ w := by
  have key : ∀ n, ∀ w : List E, w.length ≤ n →
      ((ons_firstReturnSplit e w).map (ons_edgeWeight Λ)).prod = ons_edgeWeight Λ w := by
    intro n
    induction n with
    | zero =>
        intro w hlen
        rw [Nat.le_zero, List.length_eq_zero_iff] at hlen
        subst hlen
        simp [ons_firstReturnSplit]
    | succ n ih =>
        intro w hlen
        cases w with
        | nil => simp [ons_firstReturnSplit]
        | cons x r =>
          rw [ons_firstReturnSplit]
          split
          · simp
          · rename_i e' post' hpost
            rw [List.map_cons, List.prod_cons]
            have hlensuf : (e' :: post').length ≤ n := by
              have hle := List.length_dropWhile_le (fun y => decide (y ≠ e)) r
              rw [hpost] at hle
              simp only [List.length_cons] at hlen
              omega
            rw [ih (e' :: post') hlensuf]
            have hsplit : r.takeWhile (fun y => y ≠ e) ++ (e' :: post') = r := by
              rw [← hpost]; exact List.takeWhile_append_dropWhile
            have hxr : x :: r.takeWhile (fun y => y ≠ e) ++ (e' :: post') = x :: r := by
              rw [List.cons_append, hsplit]
            have hrw : ons_edgeWeight Λ (x :: r)
                = ons_edgeWeight Λ (x :: r.takeWhile (fun y => y ≠ e) ++ [e'])
                    * ons_edgeWeight Λ (e' :: post') := by
              rw [← hxr, ons_edgeWeight_append_cons]
            rw [hrw]
  exact key w.length w le_rfl

end Split
end StatMech.Onsager
