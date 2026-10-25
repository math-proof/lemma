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
import Def.Combinatorics.BellWeakExcedance.Part5


section

namespace MetaMathlibExt

theorem mem_mins_iff {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {m : Fin n} :
    m ∈ mins P ↔ ∃ t ∈ P.parts, m ∈ t ∧ ∀ x ∈ t, m ≤ x := by
  constructor
  · intro h
    rw [mins, Finset.mem_image] at h
    obtain ⟨a, _, rfl⟩ := h
    refine ⟨P.part a, P.part_mem.mpr (Finset.mem_univ a), ?_, ?_⟩
    · exact Finset.min'_mem _ _
    · intro x hx
      exact Finset.min'_le _ _ hx
  · intro h
    obtain ⟨t, ht, hm, hle⟩ := h
    have hpart : P.part m = t := P.part_eq_of_mem ht hm
    have hmin : (P.part m).min' (P.part_nonempty.mpr (Finset.mem_univ m)) = m := by
      subst hpart
      apply le_antisymm
      · exact Finset.min'_le _ _ hm
      · have hmem : (P.part m).min' (P.part_nonempty.mpr (Finset.mem_univ m)) ∈
            P.part m :=
          Finset.min'_mem _ _
        exact hle _ hmem
    rw [mins, Finset.mem_image]
    exact ⟨m, Finset.mem_univ m, hmin⟩

theorem mem_maxs_iff {n : ℕ}
    {P : Finpartition (Finset.univ : Finset (Fin n))} {m : Fin n} :
    m ∈ maxs P ↔ ∃ t ∈ P.parts, m ∈ t ∧ ∀ x ∈ t, x ≤ m := by
  constructor
  · intro h
    rw [maxs, Finset.mem_image] at h
    obtain ⟨a, _, rfl⟩ := h
    refine ⟨P.part a, P.part_mem.mpr (Finset.mem_univ a), ?_, ?_⟩
    · exact Finset.max'_mem _ _
    · intro x hx
      exact Finset.le_max' _ _ hx
  · intro h
    obtain ⟨t, ht, hm, hle⟩ := h
    have hpart : P.part m = t := P.part_eq_of_mem ht hm
    have hmax : (P.part m).max' (P.part_nonempty.mpr (Finset.mem_univ m)) = m := by
      subst hpart
      apply le_antisymm
      · have hmem : (P.part m).max' (P.part_nonempty.mpr (Finset.mem_univ m)) ∈
            P.part m :=
          Finset.max'_mem _ _
        exact hle _ hmem
      · exact Finset.le_max' _ _ hm
    rw [maxs, Finset.mem_image]
    exact ⟨m, Finset.mem_univ m, hmax⟩

theorem card_mins_eq {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    (mins P).card = P.parts.card := by
  have himg : (mins P).image (fun m => P.part m) = P.parts := by
    ext t
    simp only [Finset.mem_image]
    constructor
    · intro h
      obtain ⟨m, hm, rfl⟩ := h
      have hmU : m ∈ (Finset.univ : Finset (Fin n)) :=
        Finset.mem_univ m
      exact P.part_mem.mpr hmU
    · intro ht
      have hne : t.Nonempty := P.nonempty_of_mem_parts ht
      have hm : t.min' hne ∈ mins P := by
        rw [mem_mins_iff]
        exact ⟨t, ht, Finset.min'_mem _ _, fun x hx => Finset.min'_le _ _ hx⟩
      refine ⟨t.min' hne, hm, ?_⟩
      exact P.part_eq_of_mem ht (Finset.min'_mem _ _)
  have hinj : Set.InjOn (fun m => P.part m) (mins P) := by
    intro m1 hm1 m2 hm2 hEq
    rw [Finset.mem_coe] at hm1 hm2
    rw [mem_mins_iff] at hm1 hm2
    obtain ⟨t1, ht1, hmem1, hle1⟩ := hm1
    obtain ⟨t2, ht2, hmem2, hle2⟩ := hm2
    have hp1 : P.part m1 = t1 := P.part_eq_of_mem ht1 hmem1
    have hp2 : P.part m2 = t2 := P.part_eq_of_mem ht2 hmem2
    have htEq : t1 = t2 := hp1.symm.trans (hEq.trans hp2)
    subst htEq
    apply le_antisymm
    · exact hle1 m2 hmem2
    · exact hle2 m1 hmem1
  have hcard := Finset.card_image_of_injOn hinj
  rw [himg] at hcard
  exact hcard.symm

theorem card_maxs_eq {n : ℕ}
    (P : Finpartition (Finset.univ : Finset (Fin n))) :
    (maxs P).card = P.parts.card := by
  have himg : (maxs P).image (fun m => P.part m) = P.parts := by
    ext t
    simp only [Finset.mem_image]
    constructor
    · intro h
      obtain ⟨m, hm, rfl⟩ := h
      have hmU : m ∈ (Finset.univ : Finset (Fin n)) :=
        Finset.mem_univ m
      exact P.part_mem.mpr hmU
    · intro ht
      have hne : t.Nonempty := P.nonempty_of_mem_parts ht
      have hm : t.max' hne ∈ maxs P := by
        rw [mem_maxs_iff]
        exact ⟨t, ht, Finset.max'_mem _ _, fun x hx => Finset.le_max' _ _ hx⟩
      refine ⟨t.max' hne, hm, ?_⟩
      exact P.part_eq_of_mem ht (Finset.max'_mem _ _)
  have hinj : Set.InjOn (fun m => P.part m) (maxs P) := by
    intro m1 hm1 m2 hm2 hEq
    rw [Finset.mem_coe] at hm1 hm2
    rw [mem_maxs_iff] at hm1 hm2
    obtain ⟨t1, ht1, hmem1, hle1⟩ := hm1
    obtain ⟨t2, ht2, hmem2, hle2⟩ := hm2
    have hp1 : P.part m1 = t1 := P.part_eq_of_mem ht1 hmem1
    have hp2 : P.part m2 = t2 := P.part_eq_of_mem ht2 hmem2
    have htEq : t1 = t2 := hp1.symm.trans (hEq.trans hp2)
    subst htEq
    apply le_antisymm
    · exact hle2 m1 hmem1
    · exact hle1 m2 hmem2
  have hcard := Finset.card_image_of_injOn hinj
  rw [himg] at hcard
  exact hcard.symm

theorem wexSet_eq_mins_toPart (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    wexSet n σ = mins (toPart n σ) := by
  ext m
  rw [mem_mins_iff]
  constructor
  · intro hm
    have hroot : root n σ m = m := root_eq_self n σ m hm
    refine ⟨(toPart n σ).part m, (toPart n σ).part_mem.mpr (Finset.mem_univ m),
      (toPart n σ).mem_part (Finset.mem_univ m), ?_⟩
    intro x hx
    rw [mem_toPart_iff] at hx
    have hle : root n σ x ≤ x := root_le n σ x
    calc m = root n σ m := hroot.symm
      _ = root n σ x := hx
      _ ≤ x := hle
  · intro h
    obtain ⟨t, ht, hmem, hle⟩ := h
    have hroot_eq : root n σ m = m := by
      have hne : t.Nonempty := (toPart n σ).nonempty_of_mem_parts ht
      obtain ⟨a, ha⟩ := hne
      have hpartEq : (toPart n σ).part a = t :=
        (toPart n σ).part_eq_of_mem ht ha
      have hrootA_mem : root n σ a ∈ t := by
        have hmem2 : root n σ a ∈ (toPart n σ).part a := by
          rw [mem_toPart_iff]
          exact (root_idem n σ a).symm
        rw [hpartEq] at hmem2
        exact hmem2
      have hle_root := hle _ hrootA_mem
      have hroot_m_eq : root n σ m = root n σ a := by
        have hm_part : m ∈ (toPart n σ).part a := by
          rw [hpartEq]
          exact hmem
        rw [mem_toPart_iff] at hm_part
        exact hm_part.symm
      have hle_m : root n σ m ≤ m := root_le n σ m
      have hge : m ≤ root n σ m := hroot_m_eq.symm ▸ hle_root
      exact le_antisymm hle_m hge
    exact root_eq_self_iff.mp hroot_eq

end MetaMathlibExt
end
