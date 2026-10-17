import Mathlib.Data.Fintype.Pi
import sympy.Basic


@[path]
private lemma main
  {n : ℕ} :
-- imply
  (Finset.univ.biUnion fun t : Fin (n + 1) =>
      Finset.univ.filter fun x : Fin (n + 1) → Fin (n + 1) =>
        Function.Bijective x ∧ x (Fin.last n) = t).card =
    ∑ t : Fin (n + 1),
      (Finset.univ.filter fun x : Fin (n + 1) → Fin (n + 1) =>
        Function.Bijective x ∧ x (Fin.last n) = t).card := by
-- proof
  classical
  rw [Finset.card_biUnion]
  intro i _ j _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro x hx hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  exact hne (hx.2.symm.trans hy.2)


-- created on 2026-10-11
-- updated on 2026-10-17
