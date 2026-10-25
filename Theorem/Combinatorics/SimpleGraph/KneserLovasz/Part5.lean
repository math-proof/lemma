/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/KneserLovasz.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Def.Combinatorics.SimpleGraph.KneserLovasz.Part6
/-!
# Kneser–Lovász theorem

For `0 < k` and `2 * k ≤ n`, the Kneser graph on the `k`-subsets of an
`n`-element set has chromatic number `n - 2 * k + 2`.
-/


namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

open Finset

theorem knUpperColoring {n k : ℕ} (hk : 0 < k) (h : 2 * k ≤ n) :
    (kneserGraph n k).Colorable (n - 2 * k + 1 + 1) := by
  classical
  refine ⟨SimpleGraph.Coloring.mk (knUpperColorFn hk) ?_⟩
  intro v w hadj
  obtain ⟨hdisj, _⟩ := hadj
  intro heq
  have hnev' : v.val.Nonempty := knUpper_nonempty hk v
  have hnew' : w.val.Nonempty := knUpper_nonempty hk w
  have e1 : (knUpperColorFn hk v).val =
      min (v.val.min' hnev').val (n - 2 * k + 1) := rfl
  have e2 : (knUpperColorFn hk w).val =
      min (w.val.min' hnew').val (n - 2 * k + 1) := rfl
  have hval : min (v.val.min' hnev').val (n - 2 * k + 1) =
      min (w.val.min' hnew').val (n - 2 * k + 1) := by
    rw [← e1, ← e2]
    exact congrArg Fin.val heq
  have hmv : v.val.min' hnev' ∈ v.val := Finset.min'_mem _ _
  have hmw : w.val.min' hnew' ∈ w.val := Finset.min'_mem _ _
  have hleV : ∀ a ∈ v.val, v.val.min' hnev' ≤ a :=
    fun a ha => (v.val.isLeast_min' hnev').2 (Finset.mem_coe.mpr ha)
  have hleW : ∀ a ∈ w.val, w.val.min' hnew' ≤ a :=
    fun a ha => (w.val.isLeast_min' hnew').2 (Finset.mem_coe.mpr ha)
  by_cases hlt : (knUpperColorFn hk v).val < n - 2 * k + 1
  · rw [e1] at hlt
    have hcN : (v.val.min' hnev').val < n - 2 * k + 1 := by omega
    have hav : (v.val.min' hnev').val = (knUpperColorFn hk v).val := by
      rw [e1]
      exact (Nat.min_eq_left (le_of_lt hcN)).symm
    have hcbN : (w.val.min' hnew').val < n - 2 * k + 1 := by omega
    have hbw : (w.val.min' hnew').val = (knUpperColorFn hk v).val := by
      have hminw : min (w.val.min' hnew').val (n - 2 * k + 1) =
          (knUpperColorFn hk v).val := by
        rw [← hval]
        exact e1.symm
      rw [← hminw]
      exact (Nat.min_eq_left (le_of_lt hcbN)).symm
    have hcn : (knUpperColorFn hk v).val < n := by omega
    have hzv : v.val.min' hnev' = ⟨(knUpperColorFn hk v).val, hcn⟩ :=
      Fin.ext hav
    have hzw : w.val.min' hnew' = ⟨(knUpperColorFn hk v).val, hcn⟩ :=
      Fin.ext hbw
    have hmem1 : (⟨(knUpperColorFn hk v).val, hcn⟩ : Fin n) ∈ v.val := hzv ▸ hmv
    have hmem2 : (⟨(knUpperColorFn hk v).val, hcn⟩ : Fin n) ∈ w.val := hzw ▸ hmw
    exact (Finset.disjoint_left.mp hdisj) hmem1 hmem2
  · have hNle : n - 2 * k + 1 ≤ (knUpperColorFn hk v).val :=
      le_of_not_gt hlt
    have hgeV : ∀ a ∈ v.val, n - 2 * k + 1 ≤ a.val := by
      intro a ha
      have h1 : v.val.min' hnev' ≤ a := hleV a ha
      have h2 : (v.val.min' hnev').val ≤ a.val := by exact_mod_cast h1
      have h3 : n - 2 * k + 1 ≤ (v.val.min' hnev').val := by omega
      omega
    have hgeW : ∀ a ∈ w.val, n - 2 * k + 1 ≤ a.val := by
      intro a ha
      have h1 : w.val.min' hnew' ≤ a := hleW a ha
      have h2 : (w.val.min' hnew').val ≤ a.val := by exact_mod_cast h1
      have h3 : n - 2 * k + 1 ≤ (w.val.min' hnew').val := by omega
      omega
    have hsubV : v.val ⊆
        Finset.univ.filter (fun a : Fin n => n - 2 * k + 1 ≤ a.val) := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hgeV a ha⟩
    have hsubW : w.val ⊆
        Finset.univ.filter (fun a : Fin n => n - 2 * k + 1 ≤ a.val) := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hgeW a ha⟩
    have hcardU : (v.val ∪ w.val).card = 2 * k := by
      have hcu := Finset.card_union_of_disjoint hdisj
      rw [hcu, v.property, w.property]
      omega
    have hcardH : (Finset.univ.filter
        (fun a : Fin n => n - 2 * k + 1 ≤ a.val)).card ≤ 2 * k - 1 := by
      have hsub : (Finset.univ.filter
          (fun a : Fin n => n - 2 * k + 1 ≤ a.val)).image Fin.val ⊆
          Finset.Ico (n - 2 * k + 1) n := by
        intro m hm
        obtain ⟨a, ha, ham⟩ := Finset.mem_image.mp hm
        have hNa := (Finset.mem_filter.mp ha).2
        rw [Finset.mem_Ico]
        constructor
        · rw [← ham]
          exact hNa
        · rw [← ham]
          exact a.2
      have hleI := Finset.card_le_card hsub
      have hIco : (Finset.Ico (n - 2 * k + 1) n).card = n - (n - 2 * k + 1) :=
        Nat.card_Ico _ _
      have himg : (Finset.univ.filter
          (fun a : Fin n => n - 2 * k + 1 ≤ a.val)).card =
          ((Finset.univ.filter
            (fun a : Fin n => n - 2 * k + 1 ≤ a.val)).image Fin.val).card :=
        (Finset.card_image_of_injective _ Fin.val_injective).symm
      omega
    have hleU : (v.val ∪ w.val).card ≤ (Finset.univ.filter
        (fun a : Fin n => n - 2 * k + 1 ≤ a.val)).card :=
      Finset.card_le_card (by
        intro a ha
        rw [Finset.mem_union] at ha
        rcases ha with h | h
        · exact hsubV h
        · exact hsubW h)
    omega

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted
