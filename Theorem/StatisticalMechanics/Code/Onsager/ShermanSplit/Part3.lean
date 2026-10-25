/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Onsager.ShermanSplit.Part3


namespace StatMech.Onsager

open Matrix BigOperators Finset Complex

set_option linter.unusedSectionVars false

section Split

variable {E : Type*} [DecidableEq E]


theorem ons_glue_firstReturnSplit (e : E) (w : List E) (hw : w.getLast? = some e) :
    ons_glue e (ons_firstReturnSplit e w) = w := by
  have key : ∀ n, ∀ w : List E, w.length ≤ n → w.getLast? = some e →
      ons_glue e (ons_firstReturnSplit e w) = w := by
    intro n
    induction n with
    | zero =>
        intro w hlen hlast
        rw [Nat.le_zero, List.length_eq_zero_iff] at hlen
        subst hlen
        simp at hlast
    | succ n ih =>
        intro w hlen hlast
        obtain ⟨x, r, rfl⟩ : ∃ x r, w = x :: r := by
          cases w with
          | nil => simp at hlast
          | cons x r => exact ⟨x, r, rfl⟩
        rw [ons_firstReturnSplit]
        split
        · 
          rw [ons_glue_cons, ons_glue_nil]
          exact List.dropLast_append_getLast? e hlast
        · 
          rename_i e' post' hpost
          rw [ons_glue_cons]
          
          have hrne : r ≠ [] := by
            rintro rfl; simp at hpost
          have hgetr : r.getLast? = some e := by
            have : (x :: r).getLast? = r.getLast? := by
              rw [show x :: r = [x] ++ r from rfl]
              exact List.getLast?_append_of_ne_nil [x] hrne
            rw [← this]; exact hlast
          have hpne : e' :: post' ≠ [] := by simp
          have hgetsuf : (e' :: post').getLast? = some e := by
            rw [← hpost]
            have hsplit : r.takeWhile (fun y => y ≠ e) ++ r.dropWhile (fun y => y ≠ e) = r :=
              List.takeWhile_append_dropWhile
            have hdrop_ne : r.dropWhile (fun y => y ≠ e) ≠ [] := by rw [hpost]; simp
            calc (r.dropWhile (fun y => y ≠ e)).getLast?
                = (r.takeWhile (fun y => y ≠ e) ++ r.dropWhile (fun y => y ≠ e)).getLast? :=
                  (List.getLast?_append_of_ne_nil _ hdrop_ne).symm
              _ = r.getLast? := by rw [hsplit]
              _ = some e := hgetr
          have hlensuf : (e' :: post').length ≤ n := by
            have hle := List.length_dropWhile_le (fun y => decide (y ≠ e)) r
            rw [hpost] at hle
            simp only [List.length_cons] at hlen
            omega
          rw [ih (e' :: post') hlensuf hgetsuf]
          
          have hdl : (x :: r.takeWhile (fun y => y ≠ e) ++ [e']).dropLast
              = x :: r.takeWhile (fun y => y ≠ e) := by
            rw [show (x :: r.takeWhile (fun y => y ≠ e) ++ [e'])
                  = (x :: r.takeWhile (fun y => y ≠ e)) ++ [e'] from rfl]
            exact List.dropLast_concat
          rw [hdl]
          rw [show x :: r.takeWhile (fun y => y ≠ e) ++ (e' :: post')
                = x :: (r.takeWhile (fun y => y ≠ e) ++ (e' :: post')) from rfl]
          rw [← hpost, List.takeWhile_append_dropWhile]
  exact key w.length w le_rfl hw


end Split
end StatMech.Onsager
