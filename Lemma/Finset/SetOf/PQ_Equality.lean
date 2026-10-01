import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ} :
-- imply
  {x : Fin (n + 1) → ℕ | Finset.univ.image x = Finset.range (n + 1) ∧ x (Fin.last n) = n} = {x : Fin (n + 1) → ℕ | Finset.univ.image (fun i : Fin n => x i.castSucc) = Finset.range n ∧ x (Fin.last n) = n} := by
-- proof
  ext x
  have hsplit : Finset.univ.image x = insert (x (Fin.last n)) (Finset.univ.image (fun i : Fin n => x i.castSucc)) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Fin.exists_fin_succ']
    exact ⟨fun h => h.elim (fun h => Or.inr h) (fun h => Or.inl h.symm), fun h => h.elim (fun h => Or.inr h.symm) (fun h => Or.inl h)⟩
  simp only [Set.mem_ofPred_eq]
  rw [hsplit]
  constructor
  · rintro ⟨h, hl⟩
    refine ⟨?_, hl⟩
    rw [hl] at h
    have hcard : (insert n (Finset.univ.image (fun i : Fin n => x i.castSucc))).card = n + 1 := by
      rw [h, Finset.card_range]
    have hS : (Finset.univ.image (fun i : Fin n => x i.castSucc)).card ≤ n :=
      Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])
    have hn : n ∉ Finset.univ.image (fun i : Fin n => x i.castSucc) := by
      intro hm
      rw [Finset.insert_eq_of_mem hm] at hcard
      omega
    rw [Finset.card_insert_of_notMem hn] at hcard
    have hsub : Finset.univ.image (fun i : Fin n => x i.castSucc) ⊆ Finset.range n := by
      intro s hs
      have hs' : s ∈ Finset.range (n + 1) := h ▸ Finset.mem_insert_of_mem hs
      have hne : s ≠ n := fun e => hn (e ▸ hs)
      rw [Finset.mem_range] at hs' ⊢
      omega
    exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range]; omega)
  · rintro ⟨h, hl⟩
    refine ⟨?_, hl⟩
    rw [hl, h, Finset.range_add_one]


-- created on 2020-07-09
