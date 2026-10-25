/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.W4PathDominoTilings.Part7
open SimpleGraph


section

namespace MetaMathlibExt

theorem above_mem_up (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) (a : Fin 4)
    (hmem : a ∈ aboveSet m M hM j) :
    ∃ k : Fin m, k.val = j + 1 ∧ partner m M hM (a, ⟨j, hj⟩) = (a, k) := by
  unfold aboveSet at hmem
  rw [vertSet_mem] at hmem
  obtain ⟨i, k, hi, hk, heq⟩ := hmem
  have hieq : i = (⟨j, hj⟩ : Fin m) := Fin.ext hi
  rw [hieq] at heq
  exact ⟨k, hk, heq⟩

theorem below_mem_down (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) (hj0 : j ≠ 0) (a : Fin 4)
    (hmem : a ∈ belowSet m M hM j) :
    ∃ k : Fin m, k.val + 1 = j ∧ partner m M hM (a, ⟨j, hj⟩) = (a, k) := by
  obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  change a ∈ vertSet m M hM j' at hmem
  rw [vertSet_mem] at hmem
  obtain ⟨i, k, hi, hk, heq⟩ := hmem
  have hkeq : k = (⟨j' + 1, hj⟩ : Fin m) := by
    apply Fin.ext
    change k.val = j' + 1
    omega
  have hsym := partner_pair_symm m M hM a i k heq
  rw [hkeq] at hsym
  exact ⟨i, by omega, hsym⟩

theorem below_above_disjoint (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) :
    Disjoint (belowSet m M hM j) (aboveSet m M hM j) := by
  rw [Finset.disjoint_left]
  intro a hb ha
  by_cases hj0 : j = 0
  · subst hj0
    unfold belowSet at hb
    exact (Finset.notMem_empty a) hb
  · obtain ⟨k1, hk1, heq1⟩ := above_mem_up m M hM j hj a ha
    obtain ⟨k2, hk2, heq2⟩ := below_mem_down m M hM j hj hj0 a hb
    have heq : (a, k1) = (a, k2) := heq1.symm.trans heq2
    have hkk : k1 = k2 := congrArg Prod.snd heq
    have hval : k1.val = k2.val := congrArg Fin.val hkk
    omega

theorem leftover_mem (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (a : Fin 4) :
    a ∈ leftoverSet m M hM j ↔ a ∉ (belowSet m M hM j ∪ aboveSet m M hM j) := by
  unfold leftoverSet
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]

theorem leftover_not_mem (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (a : Fin 4) :
    a ∉ leftoverSet m M hM j ↔ a ∈ (belowSet m M hM j ∪ aboveSet m M hM j) := by
  unfold leftoverSet
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]

theorem not_mem_union_same_layer (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) (a : Fin 4)
    (h : a ∉ (belowSet m M hM j ∪ aboveSet m M hM j)) :
    (partner m M hM (a, ⟨j, hj⟩)).2 = ⟨j, hj⟩ := by
  by_contra hne
  have ⟨haeq, hpath⟩ := partner_ne_layer_vert m M hM a ⟨j, hj⟩ hne
  have hpeq : partner m M hM (a, ⟨j, hj⟩) = (a, (partner m M hM (a, ⟨j, hj⟩)).2) := by
    ext
    · simp only [haeq]
    · rfl
  rw [pathGraph_adj] at hpath
  have hupdown : j + 1 = (partner m M hM (a, ⟨j, hj⟩)).2.val ∨
      (partner m M hM (a, ⟨j, hj⟩)).2.val + 1 = j := hpath
  rcases hupdown with hup | hdown
  · have hmem : a ∈ aboveSet m M hM j := by
      unfold aboveSet
      rw [vertSet_mem]
      exact ⟨⟨j, hj⟩, (partner m M hM (a, ⟨j, hj⟩)).2, rfl, hup.symm, hpeq⟩
    have : a ∈ (belowSet m M hM j ∪ aboveSet m M hM j) :=
      Finset.mem_union_right _ hmem
    exact h this
  · by_cases hj0 : j = 0
    · subst hj0
      omega
    · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      have hmem : a ∈ belowSet m M hM j'.succ := by
        change a ∈ vertSet m M hM j'
        rw [vertSet_mem]
        have hsym := partner_pair_symm m M hM a ⟨j'.succ, hj⟩
          (partner m M hM (a, ⟨j'.succ, hj⟩)).2 hpeq
        refine ⟨(partner m M hM (a, ⟨j'.succ, hj⟩)).2, ⟨j'.succ, hj⟩, ?_, rfl, hsym⟩
        · omega
      have : a ∈ (belowSet m M hM j'.succ ∪ aboveSet m M hM j'.succ) :=
        Finset.mem_union_left _ hmem
      exact h this

theorem horizFunNat_eq (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) (a : Fin 4) :
    horizFunNat m M hM j a =
      (if (partner m M hM (a, ⟨j, hj⟩)).2 = ⟨j, hj⟩ then
        (partner m M hM (a, ⟨j, hj⟩)).1 else a) := by
  unfold horizFunNat
  simp only [dite_eq_left hj]

theorem horizFunNat_of_mem (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) (a : Fin 4)
    (hmem : a ∈ leftoverSet m M hM j) :
    horizFunNat m M hM j a = (partner m M hM (a, ⟨j, hj⟩)).1 := by
  rw [horizFunNat_eq m M hM j hj a]
  have hnot : a ∉ (belowSet m M hM j ∪ aboveSet m M hM j) :=
    (leftover_mem m M hM j a).mp hmem
  have hsame := not_mem_union_same_layer m M hM j hj a hnot
  simp only [ite_eq_left hsame]

theorem horizFunNat_of_not_mem (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) (a : Fin 4)
    (hmem : a ∉ leftoverSet m M hM j) : horizFunNat m M hM j a = a := by
  rw [horizFunNat_eq m M hM j hj a]
  have hmemK : a ∈ (belowSet m M hM j ∪ aboveSet m M hM j) :=
    (leftover_not_mem m M hM j a).mp hmem
  have hne : (partner m M hM (a, ⟨j, hj⟩)).2 ≠ ⟨j, hj⟩ := by
    rw [Finset.mem_union] at hmemK
    rcases hmemK with hb | ha
    · by_cases hj0 : j = 0
      · subst hj0
        unfold belowSet at hb
        exact absurd hb (Finset.notMem_empty a)
      · obtain ⟨k, hk, heq⟩ := below_mem_down m M hM j hj hj0 a hb
        intro hcon
        have h1 : (partner m M hM (a, ⟨j, hj⟩)).2 = k := congrArg Prod.snd heq
        have hkk : k = (⟨j, hj⟩ : Fin m) := h1.symm.trans hcon
        have hval : k.val = j := congrArg Fin.val hkk
        omega
    · obtain ⟨k, hk, heq⟩ := above_mem_up m M hM j hj a ha
      intro hcon
      have h1 : (partner m M hM (a, ⟨j, hj⟩)).2 = k := congrArg Prod.snd heq
      have hkk : k = (⟨j, hj⟩ : Fin m) := h1.symm.trans hcon
      have hval : k.val = j := congrArg Fin.val hkk
      omega
  simp only [ite_eq_right hne]

end MetaMathlibExt
end
