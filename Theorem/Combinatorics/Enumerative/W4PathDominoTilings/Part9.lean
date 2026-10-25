/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.W4PathDominoTilings.Part11
open SimpleGraph


section

namespace MetaMathlibExt

theorem partnerT_up (m : ℕ) (t : Tiling m ∅) (a : Fin 4) (i : Fin m)
    (h : a ∈ getS m ∅ t i.val) :
    (partnerT m t (a, i)).1 = a ∧ (partnerT m t (a, i)).2.val = i.val + 1 := by
  have hup : a ∈ getS m ∅ t i.val := h
  unfold partnerT
  rw [dite_eq_left hup]
  refine ⟨rfl, rfl⟩

theorem partnerT_down (m : ℕ) (t : Tiling m ∅) (a : Fin 4) (i : Fin m)
    (h1 : a ∉ getS m ∅ t i.val)
    (h2 : a ∈ (if i.val = 0 then ∅ else getS m ∅ t (i.val - 1))) :
    (partnerT m t (a, i)).1 = a ∧ (partnerT m t (a, i)).2.val + 1 = i.val := by
  unfold partnerT
  rw [dite_eq_right h1, dite_eq_left h2]
  have hj0 : i.val ≠ 0 := by
    intro hcon
    have hempty : (if i.val = 0 then ∅ else getS m ∅ t (i.val - 1)) = ∅ := by
      simp only [ite_eq_left hcon]
    rw [hempty] at h2
    exact absurd h2 (Finset.notMem_empty a)
  refine ⟨rfl, ?_⟩
  change (i.val - 1) + 1 = i.val
  omega

theorem partnerT_horiz (m : ℕ) (t : Tiling m ∅) (a : Fin 4) (i : Fin m)
    (h1 : a ∉ getS m ∅ t i.val)
    (h2 : a ∉ (if i.val = 0 then ∅ else getS m ∅ t (i.val - 1))) :
    partnerT m t (a, i) = (getF m ∅ t i.val a, i) := by
  unfold partnerT
  rw [dite_eq_right h1, dite_eq_right h2]

theorem mem_above_up_lt (m : ℕ) (t : Tiling m ∅) (j : ℕ) (hj : j < m)
    (a : Fin 4) (h : a ∈ getS m ∅ t j) : j + 1 < m := by
  by_cases hm0 : m = 0
  · subst hm0
    exact absurd hj (Nat.not_lt_zero j)
  · by_contra hcon
    have heq : j + 1 = m := by omega
    have hjpred : j = m - 1 := by omega
    have hempty : getS m ∅ t j = ∅ := by
      rw [hjpred]
      exact getS_pred_top_empty m t (by omega)
    rw [hempty] at h
    exact absurd h (Finset.notMem_empty a)

theorem mem_below_ne_zero (m : ℕ) (t : Tiling m ∅) (j : ℕ) (a : Fin 4)
    (h : a ∈ (if j = 0 then ∅ else getS m ∅ t (j - 1))) : j ≠ 0 := by
  intro hcon
  have hempty : (if j = 0 then ∅ else getS m ∅ t (j - 1)) = ∅ := by
    simp only [ite_eq_left hcon]
  rw [hempty] at h
  exact absurd h (Finset.notMem_empty a)

theorem partnerT_involutive (m : ℕ) (t : Tiling m ∅) :
    Function.Involutive (partnerT m t) := by
  intro v
  obtain ⟨a, i⟩ := v
  have hjlt : i.val < m := i.isLt
  by_cases h_up : a ∈ getS m ∅ t i.val
  · have hj1 : i.val + 1 < m := mem_above_up_lt m t i.val hjlt a h_up
    have hpu := partnerT_up m t a i h_up
    have hp_eq : partnerT m t (a, i) = (a, ⟨i.val + 1, hj1⟩) :=
      Prod.ext hpu.1 (Fin.ext hpu.2)
    rw [hp_eq]
    have hvalk : (⟨i.val + 1, hj1⟩ : Fin m).val = i.val + 1 := rfl
    have hnot_up : a ∉ getS m ∅ t (⟨i.val + 1, hj1⟩ : Fin m).val := by
      rw [hvalk]
      have hdisj := (tiling_props m ∅ t (i.val + 1) hj1).1
      have hbelow_eq : (if i.val + 1 = 0 then ∅ else getS m ∅ t (i.val + 1 - 1)) =
          getS m ∅ t i.val := by
        have hne : i.val + 1 ≠ 0 := Nat.succ_ne_zero i.val
        simp only [ite_eq_right hne]
        have hsub : i.val + 1 - 1 = i.val := rfl
        rw [hsub]
      rw [Finset.disjoint_left] at hdisj
      have hmem : a ∈ (if i.val + 1 = 0 then ∅ else getS m ∅ t (i.val + 1 - 1)) := by
        rw [hbelow_eq]
        exact h_up
      exact hdisj hmem
    have hdown_mem : a ∈ (if (⟨i.val + 1, hj1⟩ : Fin m).val = 0 then ∅ else
        getS m ∅ t ((⟨i.val + 1, hj1⟩ : Fin m).val - 1)) := by
      rw [hvalk]
      have hne : i.val + 1 ≠ 0 := Nat.succ_ne_zero i.val
      simp only [ite_eq_right hne]
      have hsub : i.val + 1 - 1 = i.val := rfl
      rw [hsub]
      exact h_up
    have hpd := partnerT_down m t a ⟨i.val + 1, hj1⟩ hnot_up hdown_mem
    have h1 : (partnerT m t (a, ⟨i.val + 1, hj1⟩)).1 = a := hpd.1
    have h2 : (partnerT m t (a, ⟨i.val + 1, hj1⟩)).2 = i := by
      apply Fin.ext
      have hval : (partnerT m t (a, ⟨i.val + 1, hj1⟩)).2.val + 1 =
          (⟨i.val + 1, hj1⟩ : Fin m).val := hpd.2
      rw [hvalk] at hval
      omega
    exact Prod.ext h1 h2
  · by_cases h_down : a ∈ (if i.val = 0 then ∅ else getS m ∅ t (i.val - 1))
    · have hj0 : i.val ≠ 0 := mem_below_ne_zero m t i.val a h_down
      have hpd := partnerT_down m t a i h_up h_down
      have hmemS : a ∈ getS m ∅ t (i.val - 1) := by
        have heq : (if i.val = 0 then ∅ else getS m ∅ t (i.val - 1)) =
            getS m ∅ t (i.val - 1) := by
          simp only [ite_eq_right hj0]
        rw [heq] at h_down
        exact h_down
      have hkval : (partnerT m t (a, i)).2.val + 1 = i.val := hpd.2
      have h1k : (partnerT m t (a, i)).1 = a := hpd.1
      have hp_eq : partnerT m t (a, i) = (a, ⟨i.val - 1, by omega⟩) := by
        apply Prod.ext
        · exact h1k
        · apply Fin.ext
          change (partnerT m t (a, i)).2.val = i.val - 1
          omega
      rw [hp_eq]
      have hvalk : (⟨i.val - 1, by omega⟩ : Fin m).val = i.val - 1 := rfl
      have hup_mem : a ∈ getS m ∅ t (⟨i.val - 1, by omega⟩ : Fin m).val := by
        rw [hvalk]
        exact hmemS
      have hpu2 := partnerT_up m t a ⟨i.val - 1, by omega⟩ hup_mem
      have h1 : (partnerT m t (a, ⟨i.val - 1, by omega⟩)).1 = a := hpu2.1
      have h2 : (partnerT m t (a, ⟨i.val - 1, by omega⟩)).2 = i := by
        apply Fin.ext
        have hval : (partnerT m t (a, ⟨i.val - 1, by omega⟩)).2.val =
            (⟨i.val - 1, by omega⟩ : Fin m).val + 1 := hpu2.2
        rw [hvalk] at hval
        have : (partnerT m t (a, ⟨i.val - 1, by omega⟩)).2.val = i.val := by omega
        calc (partnerT m t (a, ⟨i.val - 1, by omega⟩)).2.val = i.val := this
          _ = i.val := rfl
      exact Prod.ext h1 h2
    · have hhor := partnerT_horiz m t a i h_up h_down
      rw [hhor]
      have hprops := (tiling_props m ∅ t i.val hjlt).2
      have hUmem : a ∈ Finset.univ \ ((if i.val = 0 then ∅ else getS m ∅ t (i.val - 1)) ∪
          getS m ∅ t i.val) := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
        exact fun hcon => hcon.elim h_down h_up
      obtain ⟨hbmem, hinv, _, _⟩ := hprops.1 a hUmem
      have hbmem' : getF m ∅ t i.val a ∉
          ((if i.val = 0 then ∅ else getS m ∅ t (i.val - 1)) ∪ getS m ∅ t i.val) := by
        have : getF m ∅ t i.val a ∈ Finset.univ \ ((if i.val = 0 then ∅ else
            getS m ∅ t (i.val - 1)) ∪ getS m ∅ t i.val) := hbmem
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at this
        exact this
      have hup2 : getF m ∅ t i.val a ∉ getS m ∅ t i.val := by
        intro hcon
        have : getF m ∅ t i.val a ∈ ((if i.val = 0 then ∅ else getS m ∅ t (i.val - 1)) ∪
            getS m ∅ t i.val) := Finset.mem_union_right _ hcon
        exact absurd this hbmem'
      have hdown2 : getF m ∅ t i.val a ∉
          (if i.val = 0 then ∅ else getS m ∅ t (i.val - 1)) := by
        intro hcon
        have : getF m ∅ t i.val a ∈ ((if i.val = 0 then ∅ else getS m ∅ t (i.val - 1)) ∪
            getS m ∅ t i.val) := Finset.mem_union_left _ hcon
        exact absurd this hbmem'
      have hhor2 := partnerT_horiz m t (getF m ∅ t i.val a) i hup2 hdown2
      rw [hhor2]
      have : getF m ∅ t i.val (getF m ∅ t i.val a) = a := hinv
      simp only [this]

theorem partnerT_adj (m : ℕ) (t : Tiling m ∅) (v : Fin 4 × Fin m) :
    (W4 □ pathGraph m).Adj v (partnerT m t v) := by
  obtain ⟨a, i⟩ := v
  have hjlt : i.val < m := i.isLt
  by_cases h_up : a ∈ getS m ∅ t i.val
  · have hpu := partnerT_up m t a i h_up
    have hp_eq : partnerT m t (a, i) = (a, ⟨i.val + 1, mem_above_up_lt m t i.val hjlt a h_up⟩) :=
      Prod.ext hpu.1 (Fin.ext hpu.2)
    rw [hp_eq, boxProd_adj]
    refine Or.inr ⟨?_, rfl⟩
    rw [pathGraph_adj]
    exact Or.inl rfl
  · by_cases h_down : a ∈ (if i.val = 0 then ∅ else getS m ∅ t (i.val - 1))
    · have hpd := partnerT_down m t a i h_up h_down
      have hj0 : i.val ≠ 0 := mem_below_ne_zero m t i.val a h_down
      have hp_eq : partnerT m t (a, i) = (a, ⟨i.val - 1, by omega⟩) := by
        apply Prod.ext
        · exact hpd.1
        · apply Fin.ext
          change (partnerT m t (a, i)).2.val = i.val - 1
          omega
      rw [hp_eq, boxProd_adj]
      refine Or.inr ⟨?_, rfl⟩
      rw [pathGraph_adj]
      have hval : (⟨i.val - 1, by omega⟩ : Fin m).val + 1 = i.val := by
        change (i.val - 1) + 1 = i.val
        omega
      exact Or.inr hval
    · have hhor := partnerT_horiz m t a i h_up h_down
      rw [hhor, boxProd_adj]
      refine Or.inl ⟨?_, rfl⟩
      have hprops := (tiling_props m ∅ t i.val hjlt).2
      have hUmem : a ∈ Finset.univ \ ((if i.val = 0 then ∅ else getS m ∅ t (i.val - 1)) ∪
          getS m ∅ t i.val) := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
        exact fun hcon => hcon.elim h_down h_up
      obtain ⟨_, _, _, hW⟩ := hprops.1 a hUmem
      exact hW

end MetaMathlibExt
end
