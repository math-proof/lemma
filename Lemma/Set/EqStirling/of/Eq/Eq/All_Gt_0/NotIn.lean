import sympy.sets.stirling_partition
import sympy.Basic
import Lemma.Finset.Eq.of.In.In.In_Conditionset
open Finset


@[path]
private lemma main
  {n k : ℕ}
  {x : Fin (k + 1) → Finset ℕ}
-- given
  (hcard : ∑ i, (x i).card = n + 1)
  (hunion : Finset.univ.biUnion x = Finset.range (n + 1))
  (hpos : ∀ i, 0 < (x i).card)
  (hnsing : ({n} : Finset ℕ) ∉ Finset.univ.image x) :
-- imply
  ∃ j : Fin (k + 1), ∃ a : Fin (k + 1) → Finset ℕ,
    a ∈ Stirling.conditionset n (k + 1) ∧
    ∀ i : Fin (k + 1), x i = if i = j then insert n (a i) else a i := by
-- proof
  have hx : x ∈ Stirling.conditionset (n + 1) (k + 1) := ⟨hunion, hcard, hpos⟩
  have hnU : n ∈ Finset.univ.biUnion x := by rw [hunion]; simp
  obtain ⟨j, hju, hj⟩ : ∃ j : Fin (k + 1), j ∈ Finset.univ ∧ n ∈ x j :=
    Finset.mem_biUnion.mp hnU
  have hout : ∀ i, i ≠ j → n ∉ x i := fun i hi hni =>
    hi (Eq.of.In.In.In_Conditionset hx hni hj)
  let a : Fin (k + 1) → Finset ℕ := fun i => (x i).erase n
  have ha_def : ∀ i, a i = (x i).erase n := fun i => rfl
  have hupd : ∀ i, x i = if i = j then insert n (a i) else a i := by
    intro i
    if hij : i = j then
      subst hij
      simp [ha_def, Finset.insert_erase hj]
    else
      have h : n ∉ x i := hout i hij
      simp [ha_def, hij, Finset.erase_eq_of_notMem h]
  have hc : ∀ i, (a i).card + (if i = j then 1 else 0) = (x i).card := by
    intro i
    if hij : i = j then
      subst hij
      simp [ha_def, Finset.card_erase_add_one hj]
    else
      simp [ha_def, hij, Finset.erase_eq_of_notMem (hout i hij)]
  have hbiUnion : Finset.univ.biUnion a = Finset.range n := by
    ext y
    have h1 : y ∈ Finset.univ.biUnion a ↔ ∃ i : Fin (k + 1), y ≠ n ∧ y ∈ x i := calc
        _ ↔ ∃ i : Fin (k + 1), y ∈ a i := by simp [Finset.mem_biUnion]
        _ ↔ ∃ i : Fin (k + 1), y ≠ n ∧ y ∈ x i := by
          apply exists_congr
          intro i
          rw [ha_def, Finset.mem_erase]
    rw [h1, Finset.mem_range]
    constructor
    ·
      rintro ⟨i, hy, hyn⟩
      have hU : y ∈ Finset.univ.biUnion x := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hyn⟩
      rw [hunion, Finset.mem_range] at hU
      exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hU) hy
    ·
      intro hlt
      have hU : y ∈ Finset.univ.biUnion x := by
        rw [hunion, Finset.mem_range]
        exact Nat.lt_succ_of_lt hlt
      obtain ⟨i, _, hy⟩ : ∃ i : Fin (k + 1), i ∈ Finset.univ ∧ y ∈ x i :=
        Finset.mem_biUnion.mp hU
      exact ⟨i, hlt.ne, hy⟩
  have hsumcard : ∑ i, (a i).card = n := by
    have hsum : ∑ i ∈ Finset.univ, ((a i).card + (if i = j then 1 else 0)) = ∑ i ∈ Finset.univ, (x i).card :=
      Finset.sum_congr (rfl : Finset.univ = Finset.univ) (fun i _ => hc i)
    rw [Finset.sum_add_distrib, hcard, Finset.sum_ite_eq'] at hsum
    simp at hsum
    omega
  refine ⟨j, a, ⟨hbiUnion, hsumcard, ?_⟩, hupd⟩
  intro i
  if hij : i = j then
    have hne : x j ≠ {n} := fun h => hnsing (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h⟩)
    have hpos' : 0 < ((x j).erase n).card := by
      by_contra h
      have h0 : ((x j).erase n).card = 0 := Nat.eq_zero_of_not_pos h
      have h0' : (x j).erase n = ∅ := Finset.card_eq_zero.mp h0
      have h_disj : x j = ∅ ∨ x j = {n} := (Finset.erase_eq_empty_iff (x j) n).mp h0'
      obtain (he | he) := h_disj
      ·
        exfalso
        simp [he] at hj
      ·
        exact hne he
    simpa [ha_def, hij] using hpos'
  else
    simpa [ha_def, Finset.erase_eq_of_notMem (hout i hij)] using hpos i


-- created on 2026-10-10
