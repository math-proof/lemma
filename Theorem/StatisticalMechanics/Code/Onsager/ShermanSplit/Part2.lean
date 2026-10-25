/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Onsager.ShermanSplit.Part2


namespace StatMech.Onsager

open Matrix BigOperators Finset Complex

set_option linter.unusedSectionVars false

section Glue

variable {E : Type*}


@[simp] theorem ons_glue_nil (e : E) : ons_glue e [] = [e] := rfl


theorem ons_glue_cons (e : E) (s : List E) (ss : List (List E)) :
    ons_glue e (s :: ss) = s.dropLast ++ ons_glue e ss := rfl


theorem ons_glue_head (e : E) (ss : List (List E))
    (hhead : ∀ s ∈ ss, s.head? = some e) :
    ∃ t, ons_glue e ss = e :: t := by
  induction ss with
  | nil => exact ⟨[], rfl⟩
  | cons s ss ih =>
    have hs : s.head? = some e := hhead s (by simp)
    obtain ⟨t, ht⟩ := ih (fun r hr => hhead r (by simp [hr]))
    rw [ons_glue_cons, ht]
    
    obtain ⟨s', hs'⟩ : ∃ s', s = e :: s' := by
      cases s with
      | nil => simp at hs
      | cons a s' =>
          rw [List.head?_cons, Option.some_inj] at hs
          exact ⟨s', by rw [hs]⟩
    subst hs'
    cases s' with
    | nil => exact ⟨t, rfl⟩
    | cons b s'' => exact ⟨(b :: s'').dropLast ++ e :: t, rfl⟩


theorem ons_edgeWeight_glue (Λ : Matrix E E ℂ) (e : E) (ss : List (List E))
    (hhead : ∀ s ∈ ss, s.head? = some e) (hlast : ∀ s ∈ ss, s.getLast? = some e) :
    ons_edgeWeight Λ (ons_glue e ss) = (ss.map (ons_edgeWeight Λ)).prod := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    have hsh : s.head? = some e := hhead s (by simp)
    have hsl : s.getLast? = some e := hlast s (by simp)
    have hhead' : ∀ r ∈ ss, r.head? = some e := fun r hr => hhead r (by simp [hr])
    have hlast' : ∀ r ∈ ss, r.getLast? = some e := fun r hr => hlast r (by simp [hr])
    obtain ⟨t, ht⟩ := ons_glue_head e ss hhead'
    
    have hsne : s ≠ [] := by
      rintro h; rw [h] at hsh; simp at hsh
    
    have hrecon : s.dropLast ++ [e] = s := List.dropLast_append_getLast? e hsl
    rw [ons_glue_cons, ht]
    rw [ons_edgeWeight_append_cons, ← ht, hrecon]
    rw [ih hhead' hlast']
    simp [List.map_cons]

end Glue
end StatMech.Onsager
