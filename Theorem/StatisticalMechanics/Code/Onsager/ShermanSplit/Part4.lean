/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Onsager.ShermanSplit.Part4


namespace StatMech.Onsager

open Matrix BigOperators Finset Complex

set_option linter.unusedSectionVars false

section Split

variable {E : Type*} [DecidableEq E]


theorem ons_firstReturnSegment_head {e : E} {s : List E}
    (hs : ons_isFirstReturnSegment e s) : s.head? = some e := by
  obtain ⟨interior, rfl, _⟩ := hs
  simp

theorem ons_firstReturnSegment_last {e : E} {s : List E}
    (hs : ons_isFirstReturnSegment e s) : s.getLast? = some e := by
  obtain ⟨interior, rfl, _⟩ := hs
  rw [show e :: interior ++ [e] = (e :: interior) ++ [e] from rfl]
  exact List.getLast?_concat

theorem takeWhile_ne_eq_self (e : E) (l : List E)
    (h : ∀ x ∈ l, x ≠ e) : l.takeWhile (fun x => x ≠ e) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hx : x ≠ e := h x (by simp)
      have hxs : ∀ y ∈ xs, y ≠ e := by
        intro y hy
        exact h y (by simp [hy])
      have hxb : decide (x ≠ e) = true := by simp [hx]
      rw [List.takeWhile_cons, if_pos hxb, ih hxs]

theorem dropWhile_ne_eq_nil (e : E) (l : List E)
    (h : ∀ x ∈ l, x ≠ e) : l.dropWhile (fun x => x ≠ e) = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      have hx : x ≠ e := h x (by simp)
      have hxs : ∀ y ∈ xs, y ≠ e := by
        intro y hy
        exact h y (by simp [hy])
      have hxb : decide (x ≠ e) = true := by simp [hx]
      rw [List.dropWhile_cons, if_pos hxb, ih hxs]

theorem dropWhile_head_eq_root (e : E) {l : List E} {x : E} {xs : List E}
    (h : l.dropWhile (fun y => y ≠ e) = x :: xs) : x = e := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
      rw [List.dropWhile_cons] at h
      by_cases hy : y ≠ e
      · have hyb : decide (y ≠ e) = true := by simp [hy]
        rw [if_pos hyb] at h
        exact ih h
      · have hyb : ¬ decide (y ≠ e) = true := by simp [hy]
        rw [if_neg hyb] at h
        have hy' : y = e := not_ne_iff.mp hy
        injection h with hxy _
        exact hxy.symm.trans hy'


theorem ons_firstReturnSplit_glue (e : E) (ss : List (List E))
    (hfirst : ∀ s ∈ ss, ons_isFirstReturnSegment e s) :
    ons_firstReturnSplit e (ons_glue e ss) = ss ++ [[e]] := by
  induction ss with
  | nil => simp [ons_firstReturnSplit]
  | cons s ss ih =>
      have hs := hfirst s (by simp)
      obtain ⟨interior, hsform, hinterior⟩ := hs
      subst s
      have hfirst' : ∀ t ∈ ss, ons_isFirstReturnSegment e t := by
        intro t ht
        exact hfirst t (by simp [ht])
      have hhead : ∀ t ∈ ss, t.head? = some e := by
        intro t ht
        exact ons_firstReturnSegment_head (hfirst' t ht)
      obtain ⟨tail, hglue⟩ := ons_glue_head e ss hhead
      have htake : interior.takeWhile (fun x => x ≠ e) = interior :=
        takeWhile_ne_eq_self e interior hinterior
      have hdrop : interior.dropWhile (fun x => x ≠ e) = [] :=
        dropWhile_ne_eq_nil e interior hinterior
      have htakeAll :
          (interior ++ e :: tail).takeWhile (fun x => x ≠ e) = interior := by
        rw [List.takeWhile_append, htake]
        simp
      have hdropAll :
          (interior ++ e :: tail).dropWhile (fun x => x ≠ e) = e :: tail := by
        rw [List.dropWhile_append, hdrop]
        simp
      rw [ons_glue_cons]
      have hdl : (e :: interior ++ [e]).dropLast = e :: interior := by
        rw [show e :: interior ++ [e] = (e :: interior) ++ [e] from rfl]
        exact List.dropLast_concat
      rw [hdl, hglue]
      change ons_firstReturnSplit e (e :: (interior ++ e :: tail)) = _
      rw [ons_firstReturnSplit]
      rw [hdropAll]
      simp only [htakeAll]
      rw [← hglue, ih hfirst']
      simp


theorem ons_firstReturnSplit_closed (e : E) (w : List E)
    (hhead : w.head? = some e) (hlast : w.getLast? = some e) :
    ∃ ss : List (List E),
      ons_firstReturnSplit e w = ss ++ [[e]] ∧
      ∀ s ∈ ss, ons_isFirstReturnSegment e s := by
  have key : ∀ n, ∀ w : List E, w.length ≤ n → w.head? = some e →
      w.getLast? = some e →
      ∃ ss : List (List E),
        ons_firstReturnSplit e w = ss ++ [[e]] ∧
        ∀ s ∈ ss, ons_isFirstReturnSegment e s := by
    intro n
    induction n with
    | zero =>
        intro w hlen hhead _
        rw [Nat.le_zero, List.length_eq_zero_iff] at hlen
        subst w
        simp at hhead
    | succ n ih =>
        intro w hlen hhead hlast
        obtain ⟨x, r, rfl⟩ : ∃ x r, w = x :: r := by
          cases w with
          | nil => simp at hhead
          | cons x r => exact ⟨x, r, rfl⟩
        have hx : x = e := by simpa using hhead
        subst x
        rw [ons_firstReturnSplit]
        split
        · rename_i hpost
          have hr : r = [] := by
            by_contra hrne
            obtain ⟨y, ys, rfl⟩ : ∃ y ys, r = y :: ys := by
              cases r with
              | nil => exact absurd rfl hrne
              | cons y ys => exact ⟨y, ys, rfl⟩
            have hlast' : (y :: ys).getLast? = some e := by
              simpa only [List.getLast?_cons_cons] using hlast
            obtain ⟨zs, hzs⟩ := List.getLast?_eq_some_iff.mp hlast'
            have hemem : e ∈ y :: ys := by
              rw [hzs]
              simp
            have hall := (List.dropWhile_eq_nil_iff.mp hpost) e hemem
            simp at hall
          subst r
          exact ⟨[], by simp, by simp⟩
        · rename_i e' post hpost
          have he' : e' = e := dropWhile_head_eq_root e hpost
          subst e'
          have hsegment : ons_isFirstReturnSegment e
              (e :: r.takeWhile (fun y => y ≠ e) ++ [e]) := by
            refine ⟨r.takeWhile (fun y => y ≠ e), rfl, ?_⟩
            intro y hy
            have hy' : decide (y ≠ e) = true :=
              List.mem_takeWhile_imp (p := fun z : E => decide (z ≠ e)) hy
            exact of_decide_eq_true hy'
          have hrne : r ≠ [] := by
            rintro rfl
            simp at hpost
          have hgetr : r.getLast? = some e := by
            have hlastCons : (e :: r).getLast? = r.getLast? := by
              rw [show e :: r = [e] ++ r from rfl]
              exact List.getLast?_append_of_ne_nil [e] hrne
            rw [← hlastCons]
            exact hlast
          have hsufLast : (e :: post).getLast? = some e := by
            rw [← hpost]
            have hdropNe : r.dropWhile (fun y => y ≠ e) ≠ [] := by
              rw [hpost]
              simp
            calc
              (r.dropWhile (fun y => y ≠ e)).getLast? =
                  (r.takeWhile (fun y => y ≠ e) ++
                    r.dropWhile (fun y => y ≠ e)).getLast? :=
                (List.getLast?_append_of_ne_nil _ hdropNe).symm
              _ = r.getLast? := by rw [List.takeWhile_append_dropWhile]
              _ = some e := hgetr
          have hsufLen : (e :: post).length ≤ n := by
            have hle := List.length_dropWhile_le (fun y => decide (y ≠ e)) r
            rw [hpost] at hle
            simp only [List.length_cons] at hlen
            omega
          obtain ⟨ss, hsplit, hvalid⟩ :=
            ih (e :: post) hsufLen (by simp) hsufLast
          refine ⟨(e :: r.takeWhile (fun y => y ≠ e) ++ [e]) :: ss, ?_, ?_⟩
          · rw [hsplit]
            rfl
          · intro s hs
            simp only [List.mem_cons] at hs
            rcases hs with rfl | hs
            · exact hsegment
            · exact hvalid s hs
  exact key w.length w le_rfl hhead hlast

theorem list_count_eq_sum_indicator (e : E) (l : List E) :
    l.count e = (l.map fun x => if x = e then 1 else 0).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.count_cons, List.map_cons, List.sum_cons, ih]
      by_cases hx : x = e <;> simp [hx, beq_iff_eq] <;> omega


theorem ons_count_ofFn_eq_visitCount (e : E) {n : ℕ} (v : Fin n → E) :
    (List.ofFn v).count e = Fintype.card {k : Fin n // v k = e} := by
  rw [list_count_eq_sum_indicator, List.map_ofFn, List.sum_ofFn]
  change (∑ k : Fin n, if v k = e then 1 else 0) = _
  rw [Finset.sum_boole]
  rw [← Finset.card_subtype]
  simp


theorem ons_glue_append_terminal (e : E) (ss : List (List E)) :
    ons_glue e (ss ++ [[e]]) = ons_glue e ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
      rw [List.cons_append, ons_glue_cons, ons_glue_cons, ih]


theorem ons_count_glue_firstReturn (e : E) (ss : List (List E))
    (hfirst : ∀ s ∈ ss, ons_isFirstReturnSegment e s) :
    (ons_glue e ss).count e = ss.length + 1 := by
  induction ss with
  | nil => simp [ons_glue]
  | cons s ss ih =>
      have hs := hfirst s (by simp)
      obtain ⟨interior, hsform, hinterior⟩ := hs
      subst s
      have hfirst' : ∀ t ∈ ss, ons_isFirstReturnSegment e t := by
        intro t ht
        exact hfirst t (by simp [ht])
      have hcountInterior : interior.count e = 0 := by
        rw [List.count_eq_zero]
        intro he
        exact hinterior e he rfl
      rw [ons_glue_cons]
      have hdl : (e :: interior ++ [e]).dropLast = e :: interior := by
        rw [show e :: interior ++ [e] = (e :: interior) ++ [e] from rfl]
        exact List.dropLast_concat
      rw [hdl, List.count_append, List.count_cons, hcountInterior, ih hfirst']
      simp
      omega


end Split
end StatMech.Onsager
