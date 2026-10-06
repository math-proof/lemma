import sympy.functions.special.tensor_functions
import Lemma.Nat.Delta.eq.Ite
import sympy.Basic


@[main]
private lemma main
  {x y : ℂ}
  {a : ℕ → ℂ}
-- given
  (h : ({x, y} : Finset ℂ) = {a 0, a 1}) :
-- imply
  (x, y) = (a (1 - KroneckerDelta (a 0) x), a (KroneckerDelta (a 0) x)) := by
-- proof
  have hx : x = a 0 ∨ x = a 1 := by
    have : x ∈ ({x, y} : Finset ℂ) := by simp
    rw [h] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    tauto
  have hy : y = a 0 ∨ y = a 1 := by
    have : y ∈ ({x, y} : Finset ℂ) := by simp
    rw [h] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    tauto
  have ha0 : a 0 = x ∨ a 0 = y := by
    have : a 0 ∈ ({a 0, a 1} : Finset ℂ) := by simp
    rw [←h] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    tauto
  have ha1 : a 1 = x ∨ a 1 = y := by
    have : a 1 ∈ ({a 0, a 1} : Finset ℂ) := by simp
    rw [←h] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    tauto
  rw [Prod.ext_iff]
  rw [Nat.Delta.eq.Ite (a 0) x]
  split_ifs with heq
  · constructor
    · exact heq.symm
    · obtain hy0 | hy1 := hy
      · obtain h1 | h1 := ha1
        · exact (h1.trans (heq.symm.trans hy0.symm)).symm
        · exact h1.symm
      · exact hy1
  · constructor
    · obtain h0 | h1 := hx
      · exact False.elim (heq h0.symm)
      · exact h1
    · obtain h0 | h1 := ha0
      · exact False.elim (heq h0)
      · exact h1.symm


-- created on 2021-04-02
-- updated on 2023-05-17
