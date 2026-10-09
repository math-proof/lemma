import sympy.sets.stirling_partition
import sympy.Basic
import Lemma.Finset.Subset_Range.of.In_Conditionset
import Lemma.Finset.Eq.of.In.In.In_Conditionset
open Finset Stirling.conditionset


@[path]
private lemma main
  {n k : ℕ} :
-- imply
  {e | e ∈ (fun x : Fin (k + 1) → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset (n + 1) (k + 1) ∧ ({n} : Finset ℕ) ∉ e} =
    ⋃ j : Fin (k + 1), (fun x : Fin (k + 1) → Finset ℕ => Finset.univ.image (Function.update x j (insert n (x j)))) '' Stirling.conditionset n (k + 1) := by
-- proof
  ext e
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image]
  constructor
  ·
    rintro ⟨⟨x, hx, rfl⟩, hne⟩
    have hnU : n ∈ Finset.univ.biUnion x := by rw [hx.1]; simp
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hnU
    have hout : ∀ i, i ≠ j → n ∉ x i := fun i hi hni => hi (Eq.of.In.In.In_Conditionset hx hni hj)
    set y : Fin (k + 1) → Finset ℕ := fun i => (x i).erase n with hy
    have hupd : Function.update y j (insert n (y j)) = x := by
      funext i
      if hij : i = j then
        subst hij
        simp [hy, Finset.insert_erase hj]
      else
        rw [Function.update_of_ne hij, hy]
        exact Finset.erase_eq_of_notMem (hout i hij)
    refine ⟨j, y, ⟨?_, ?_, ?_⟩, by rw [hupd]⟩
    ·
      ext a
      have hU := congrArg (a ∈ ·) hx.1
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range, eq_iff_iff] at hU
      simp only [hy, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range, Finset.mem_erase]
      constructor
      ·
        rintro ⟨i, hne', hi⟩
        have := hU.mp ⟨i, hi⟩
        omega
      ·
        intro ha
        obtain ⟨i, hi⟩ := hU.mpr (by omega)
        exact ⟨i, by omega, hi⟩
    ·
      have hc : ∀ i, (y i).card + (if i = j then 1 else 0) = (x i).card := by
        intro i
        if hij : i = j then
          subst hij
          simp [hy, Finset.card_erase_add_one hj]
        else
          simp [hy, hij, Finset.erase_eq_of_notMem (hout i hij)]
      have := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hc i)
      rw [Finset.sum_add_distrib, hx.2.1, Finset.sum_ite_eq'] at this
      simp at this
      omega
    ·
      intro i
      if hij : i = j then
        subst hij
        have hxj : x i ≠ {n} := fun h => hne (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩)
        have h1 : 1 < (x i).card := by
          by_contra hle
          have hc1 : (x i).card = 1 := by have := hx.2.2 i; omega
          obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc1
          rw [ha] at hj hxj
          simp at hj
          exact hxj (by rw [hj])
        have := Finset.card_erase_add_one hj
        simp only [hy]
        omega
      else
        simp only [hy, Finset.erase_eq_of_notMem (hout i hij)]
        exact hx.2.2 i
  ·
    rintro ⟨j, x, hx, rfl⟩
    have hsub := Subset_Range.of.In_Conditionset hx
    have hnj : n ∉ x j := fun h => by simpa using hsub j h
    refine ⟨⟨Function.update x j (insert n (x j)), ⟨?_, ?_, ?_⟩, rfl⟩, ?_⟩
    ·
      ext a
      have hU := congrArg (a ∈ ·) hx.1
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range, eq_iff_iff] at hU
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      ·
        rintro ⟨i, hi⟩
        if hij : i = j then
          subst hij
          rw [Function.update_self, Finset.mem_insert] at hi
          obtain rfl | hi := hi
          · omega
          · have := hU.mp ⟨i, hi⟩; omega
        else
          rw [Function.update_of_ne hij] at hi
          have := hU.mp ⟨i, hi⟩; omega
      ·
        intro ha
        if han : a = n then
          exact ⟨j, by rw [Function.update_self, han]; exact Finset.mem_insert_self _ _⟩
        else
          obtain ⟨i, hi⟩ := hU.mpr (by omega)
          by_cases hij : i = j
          ·
            subst hij
            exact ⟨i, by rw [Function.update_self]; exact Finset.mem_insert_of_mem hi⟩
          · exact ⟨i, by rw [Function.update_of_ne hij]; exact hi⟩
    ·
      have hc : ∀ i, (Function.update x j (insert n (x j)) i).card = (x i).card + (if i = j then 1 else 0) := by
        intro i
        if hij : i = j then
          subst hij
          simp [Finset.card_insert_of_notMem hnj]
        else
          simp [hij]
      rw [Finset.sum_congr rfl (fun i _ => hc i), Finset.sum_add_distrib, hx.2.1, Finset.sum_ite_eq']
      simp
    ·
      intro i
      if hij : i = j then
        subst hij
        rw [Function.update_self]
        exact Finset.card_pos.mpr ⟨n, Finset.mem_insert_self _ _⟩
      else
        rw [Function.update_of_ne hij]
        exact hx.2.2 i
    ·
      intro hmem
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
      if hij : i = j then
        subst hij
        rw [Function.update_self] at hi
        have hxe : x i ⊆ {n} := fun a ha => hi ▸ Finset.mem_insert_of_mem ha
        obtain ⟨a, ha⟩ := Finset.card_pos.mp (hx.2.2 i)
        have := hxe ha
        rw [Finset.mem_singleton] at this
        exact hnj (this ▸ ha)
      else
        rw [Function.update_of_ne hij] at hi
        have := hsub i (hi ▸ Finset.mem_singleton_self n)
        simp at this


-- created on 2026-10-07
