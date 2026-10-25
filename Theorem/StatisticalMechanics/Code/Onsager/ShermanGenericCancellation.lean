/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanGenericCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanListSeries.Part2
import Theorem.StatisticalMechanics.Code.Onsager.ShermanReroot.Part4
import Def.StatisticalMechanics.Code.Onsager.ShermanGenericCancellation


namespace StatMech.Onsager

open Matrix BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem mem_glue_of_mem_segment (e : E) (ss : List (List E))
    (hfirst : ∀ s ∈ ss, ons_isFirstReturnSegment e s)
    {s : List E} (hs : s ∈ ss) {x : E} (hx : x ∈ s) :
    x ∈ ons_glue e ss := by
  induction ss generalizing s x with
  | nil => simp at hs
  | cons t ts ih =>
      have ht := hfirst t (by simp)
      have hfirst' : ∀ u ∈ ts, ons_isFirstReturnSegment e u := by
        intro u hu
        exact hfirst u (by simp [hu])
      simp only [List.mem_cons] at hs
      rw [ons_glue_cons]
      rw [List.mem_append]
      rcases hs with hst | hs
      · rw [hst] at hx
        obtain ⟨interior, htform, _⟩ := ht
        have hdl : t.dropLast = e :: interior := by
          rw [htform, show e :: interior ++ [e] = (e :: interior) ++ [e] from rfl]
          exact List.dropLast_concat
        rw [hdl]
        rw [htform,
          show e :: interior ++ [e] = (e :: interior) ++ [e] from rfl,
          List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | hxe
        · exact Or.inl hx
        · right
          rw [hxe]
          have hhead : ∀ u ∈ ts, u.head? = some e := by
            intro u hu
            exact ons_firstReturnSegment_head (hfirst' u hu)
          obtain ⟨tail, htail⟩ := ons_glue_head e ts hhead
          rw [htail]
          simp
      · exact Or.inr (ih hfirst' hs hx)

theorem glue_getLast (e : E) (ss : List (List E)) :
    (ons_glue e ss).getLast? = some e := by
  induction ss with
  | nil => simp [ons_glue]
  | cons s ss ih =>
      rw [ons_glue_cons]
      have hne : ons_glue e ss ≠ [] := by
        intro h
        rw [h] at ih
        simp at ih
      rw [List.getLast?_append_of_ne_nil _ hne, ih]

theorem avoids_glue (e r : E) (her : e ≠ r) (ss : List (List E))
    (hvalid : ons_validFactorList e r ss) :
    ∀ x ∈ ons_glue e ss, x ≠ r := by
  induction ss with
  | nil => simpa [ons_glue] using her
  | cons s ss ih =>
      rw [ons_glue_cons]
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact (hvalid s (by simp)).2 x (List.mem_of_mem_dropLast hx)
      · apply ih
        · intro t ht
          exact hvalid t (by simp [ht])
        · exact hx

theorem firstReturnFactors_valid (e r : E) (w : List E)
    (hw : ons_validRootedList e r w) :
    ons_validFactorList e r (ons_firstReturnFactors e w) := by
  have hspec := ons_firstReturnFactors_spec e w hw.1 hw.2.1
  intro s hs
  refine ⟨hspec.2.1 s hs, ?_⟩
  intro x hx
  apply hw.2.2 x
  rw [← hspec.2.2]
  exact mem_glue_of_mem_segment e _ hspec.2.1 hs hx


end StatMech.Onsager
