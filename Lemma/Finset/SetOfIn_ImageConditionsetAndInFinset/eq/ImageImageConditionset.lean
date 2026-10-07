import sympy.sets.stirling_partition
import sympy.Basic
import Lemma.Finset.Eq.of.In.In.In_Conditionset
open Finset Stirling.conditionset


@[main]
private lemma main
  {n k : ℕ} :
-- imply
  {e | e ∈ (fun x : Fin (k + 1) → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset (n + 1) (k + 1) ∧ ({n} : Finset ℕ) ∈ e} =
    (fun e : Finset (Finset ℕ) => insert ({n} : Finset ℕ) e) '' ((fun x : Fin k → Finset ℕ => Finset.univ.image x) '' Stirling.conditionset n k) := by
-- proof
  ext e
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  ·
    rintro ⟨⟨x, hx, rfl⟩, hmem⟩
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
    have hout : ∀ i, i ≠ j → n ∉ x i := fun i hi hni => hi (Eq.of.In.In.In_Conditionset hx hni (by rw [hj]; exact Finset.mem_singleton_self n))
    refine ⟨Finset.univ.image (fun i : Fin k => x (j.succAbove i)), ⟨fun i => x (j.succAbove i), ⟨?_, ?_, ?_⟩, rfl⟩, ?_⟩
    ·
      ext a
      have hU := congrArg (a ∈ ·) hx.1
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range, eq_iff_iff] at hU ⊢
      constructor
      ·
        rintro ⟨i, hi⟩
        have h1 := hU.mp ⟨_, hi⟩
        have : a ≠ n := fun h => hout _ (Fin.succAbove_ne j i) (h ▸ hi)
        omega
      ·
        intro ha
        obtain ⟨i, hi⟩ := hU.mpr (by omega)
        have hij : i ≠ j := by
          rintro rfl
          rw [hj, Finset.mem_singleton] at hi
          omega
        obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hij
        exact ⟨z, hz ▸ hi⟩
    ·
      have := hx.2.1
      rw [Fin.sum_univ_succAbove _ j, hj, Finset.card_singleton] at this
      show ∑ i, (x (j.succAbove i)).card = n
      omega
    ·
      intro i
      exact hx.2.2 _
    ·
      ext P
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      ·
        rintro (rfl | ⟨i, rfl⟩)
        · exact ⟨j, hj⟩
        · exact ⟨_, rfl⟩
      ·
        rintro ⟨i, rfl⟩
        if hij : i = j then
          subst hij
          exact Or.inl hj
        else
          obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hij
          exact Or.inr ⟨z, by rw [hz]⟩
  ·
    rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨⟨(Fin.cons ({n} : Finset ℕ) y : Fin (k + 1) → Finset ℕ), ⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
    ·
      ext a
      have hU := congrArg (a ∈ ·) hy.1
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range, eq_iff_iff] at hU ⊢
      rw [Fin.exists_fin_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Finset.mem_singleton]
      constructor
      ·
        rintro (rfl | ⟨i, hi⟩)
        · omega
        ·
          have := hU.mp ⟨i, hi⟩
          omega
      ·
        intro ha
        if han : a = n then
          exact Or.inl han
        else
          exact Or.inr (hU.mpr (by omega))
    ·
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Finset.card_singleton, hy.2.1]
      omega
    ·
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · simpa using hy.2.2 i
    ·
      ext P
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
      rw [Fin.exists_fin_succ]
      constructor
      ·
        rintro (h | ⟨i, h⟩)
        ·
          left
          rw [← h, Fin.cons_zero]
        ·
          right
          exact ⟨i, by rw [← h, Fin.cons_succ]⟩
      ·
        rintro (h | ⟨i, h⟩)
        ·
          left
          rw [h, Fin.cons_zero]
        ·
          right
          exact ⟨i, by rw [← h, Fin.cons_succ]⟩
    · exact Finset.mem_insert_self _ _


-- created on 2026-10-07
