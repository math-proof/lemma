/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Bound
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Def.Combinatorics.BellWeakExcedance.Part7


section

namespace MetaMathlibExt

theorem succ_mem {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {y : Fin n}
    (hy : y ∉ maxs P) : succ P y hy ∈ P.part y := by
  have hmem : succ P y hy ∈ (P.part y).filter (fun x => y < x) := by
    unfold succ
    exact Finset.min'_mem _ _
  exact Finset.mem_of_mem_filter _ hmem

theorem lt_succ {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {y : Fin n}
    (hy : y ∉ maxs P) : y < succ P y hy := by
  have hmem : succ P y hy ∈ (P.part y).filter (fun x => y < x) := by
    unfold succ
    exact Finset.min'_mem _ _
  exact (Finset.mem_filter.mp hmem).2

theorem succ_le_of_mem {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {y x : Fin n}
    (hy : y ∉ maxs P) (hxB : x ∈ P.part y) (hyx : y < x) :
    succ P y hy ≤ x := by
  have hmem : x ∈ (P.part y).filter (fun z => y < z) :=
    Finset.mem_filter.mpr ⟨hxB, hyx⟩
  unfold succ
  exact Finset.min'_le _ _ hmem

theorem succ_not_mem_mins {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {y : Fin n}
    (hy : y ∉ maxs P) : succ P y hy ∉ mins P := by
  intro hmem
  rw [mem_mins_iff] at hmem
  obtain ⟨t, ht, hmem2, hle⟩ := hmem
  have hsucc_mem : succ P y hy ∈ P.part y := succ_mem hy
  have hpart_eq : P.part (succ P y hy) = P.part y := by
    have h1 : P.part (succ P y hy) ∈ P.parts :=
      P.part_mem.mpr (Finset.mem_univ _)
    have h2 : P.part y ∈ P.parts := P.part_mem.mpr (Finset.mem_univ y)
    exact P.eq_of_mem_parts h1 h2
      (P.mem_part (Finset.mem_univ _)) hsucc_mem
  have ht_eq : t = P.part y := by
    have h1 : P.part (succ P y hy) = t :=
      P.part_eq_of_mem ht hmem2
    rw [hpart_eq] at h1
    exact h1.symm
  subst ht_eq
  have hne : (P.part y).Nonempty := P.part_nonempty.mpr (Finset.mem_univ y)
  have hmin_le : succ P y hy ≤ (P.part y).min' hne := by
    have hmem_min : (P.part y).min' hne ∈ P.part y := Finset.min'_mem _ _
    exact hle _ hmem_min
  have hmin_lt : (P.part y).min' hne < succ P y hy := by
    have hle_min : (P.part y).min' hne ≤ y := by
      have hy_mem : y ∈ P.part y := P.mem_part (Finset.mem_univ y)
      exact Finset.min'_le _ _ hy_mem
    have hlt : y < succ P y hy := lt_succ hy
    exact lt_of_le_of_lt hle_min hlt
  exact absurd hmin_le (not_le_of_gt hmin_lt)

theorem pred_succ_eq {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {y : Fin n}
    (hy : y ∉ maxs P) :
    pred P (succ P y hy) (succ_not_mem_mins hy) = y := by
  have hsucc_mem : succ P y hy ∈ P.part y := succ_mem hy
  have hpart_eq : P.part (succ P y hy) = P.part y := by
    have h1 : P.part (succ P y hy) ∈ P.parts :=
      P.part_mem.mpr (Finset.mem_univ _)
    have h2 : P.part y ∈ P.parts := P.part_mem.mpr (Finset.mem_univ y)
    exact P.eq_of_mem_parts h1 h2
      (P.mem_part (Finset.mem_univ _)) hsucc_mem
  have hy_mem_part_succ : y ∈ P.part (succ P y hy) := by
    rw [hpart_eq]
    exact P.mem_part (Finset.mem_univ y)
  have hlt_y : y < succ P y hy := lt_succ hy
  have hle1 : y ≤ pred P (succ P y hy) (succ_not_mem_mins hy) := by
    apply le_pred_of_mem _ hy_mem_part_succ hlt_y
  have hle2 : pred P (succ P y hy) (succ_not_mem_mins hy) ≤ y := by
    have hpred_mem : pred P (succ P y hy) (succ_not_mem_mins hy) ∈
        P.part (succ P y hy) :=
      pred_mem _
    have hpred_lt : pred P (succ P y hy) (succ_not_mem_mins hy) < succ P y hy :=
      pred_lt _
    rw [hpart_eq] at hpred_mem
    rcases lt_trichotomy (pred P (succ P y hy) (succ_not_mem_mins hy)) y with
      hlt | heq | hgt
    · exact le_of_lt hlt
    · exact le_of_eq heq
    · have hsucc_le : succ P y hy ≤ pred P (succ P y hy) (succ_not_mem_mins hy) := by
        apply succ_le_of_mem hy hpred_mem hgt
      have hcontra : succ P y hy < succ P y hy :=
        lt_of_le_of_lt hsucc_le hpred_lt
      exact absurd hcontra (lt_irrefl _)
  exact le_antisymm hle2 hle1

theorem pred_injective {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))}
    {u1 u2 : Fin n} {hu1 : u1 ∉ mins P} {hu2 : u2 ∉ mins P}
    (hEq : pred P u1 hu1 = pred P u2 hu2) : u1 = u2 := by
  have hB1mem : P.part u1 ∈ P.parts := P.part_mem.mpr (Finset.mem_univ u1)
  have hB2mem : P.part u2 ∈ P.parts := P.part_mem.mpr (Finset.mem_univ u2)
  have hpred1_mem : pred P u1 hu1 ∈ P.part u1 := pred_mem hu1
  have hpred2_mem : pred P u2 hu2 ∈ P.part u2 := pred_mem hu2
  have hBeq : P.part u1 = P.part u2 := by
    have hmem1 : pred P u1 hu1 ∈ P.part u1 := hpred1_mem
    have hmem2 : pred P u1 hu1 ∈ P.part u2 := hEq ▸ hpred2_mem
    exact P.eq_of_mem_parts hB1mem hB2mem hmem1 hmem2
  have hu1_mem : u1 ∈ P.part u2 := by
    rw [← hBeq]
    exact P.mem_part (Finset.mem_univ u1)
  have hu2_mem : u2 ∈ P.part u1 := by
    rw [hBeq]
    exact P.mem_part (Finset.mem_univ u2)
  rcases lt_trichotomy u1 u2 with hlt | heq | hgt
  · have hle : u1 ≤ pred P u2 hu2 :=
      le_pred_of_mem hu2 hu1_mem hlt
    have hlt2 : pred P u1 hu1 < u1 := pred_lt hu1
    rw [hEq] at hlt2
    exact absurd (lt_of_lt_of_le hlt2 hle) (lt_irrefl _)
  · exact heq
  · have hle : u2 ≤ pred P u1 hu1 :=
      le_pred_of_mem hu1 hu2_mem hgt
    have hlt2 : pred P u2 hu2 < u2 := pred_lt hu2
    rw [← hEq] at hlt2
    exact absurd (lt_of_lt_of_le hlt2 hle) (lt_irrefl _)

theorem pred_not_mem_maxs {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {u : Fin n}
    (hu : u ∉ mins P) : pred P u hu ∉ maxs P := by
  intro hmem
  rw [mem_maxs_iff] at hmem
  obtain ⟨t, ht, hmem2, hle⟩ := hmem
  have hpred_mem : pred P u hu ∈ P.part u := pred_mem hu
  have hpart_mem : P.part u ∈ P.parts := P.part_mem.mpr (Finset.mem_univ u)
  have htEq : t = P.part u := by
    have h1 : P.part (pred P u hu) = t :=
      P.part_eq_of_mem ht hmem2
    have h2 : P.part (pred P u hu) = P.part u := by
      have h1' : P.part (pred P u hu) ∈ P.parts :=
        P.part_mem.mpr (Finset.mem_univ _)
      exact P.eq_of_mem_parts h1' hpart_mem
        (P.mem_part (Finset.mem_univ _)) hpred_mem
    rw [h2] at h1
    exact h1.symm
  subst htEq
  have hu_le : u ≤ pred P u hu := hle u (P.mem_part (Finset.mem_univ u))
  have hlt : pred P u hu < u := pred_lt hu
  exact absurd hu_le (not_le_of_gt hlt)

end MetaMathlibExt
end
