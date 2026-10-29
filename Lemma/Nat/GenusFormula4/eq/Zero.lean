import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.ModularCurve_GenusNumerics
open ModularCurve


/-- ported from external source -/

private lemma  divisors_eq : Nat.divisors 4 = {1, 2, 4} := by decide

private lemma  dedekindPsi_eq : dedekindPsi 4 = 6 := by
  rw [dedekindPsi, divisors_eq]
  have h1 : Squarefree (1 : ℕ) := squarefree_one
  have h2 : Squarefree (2 : ℕ) := Nat.prime_two.prime.squarefree
  have h4 : ¬ Squarefree (4 : ℕ) := fun h => by
    have := h 2 ⟨1, by norm_num⟩
    rw [Nat.isUnit_iff] at this; omega
  rw [Finset.filter_insert, ite_eq_left h1, Finset.filter_insert, ite_eq_left h2, Finset.filter_singleton, ite_eq_right h4]
  decide

private lemma  cuspCount_eq : cuspCount 4 = 3 := by decide

private lemma  nuTwo_eq : nuTwo 4 = 0 := by
  rw [nuTwo, Nat.card_eq_fintype_card]; decide

private lemma  nuThree_eq : nuThree 4 = 0 := by
  rw [nuThree, Nat.card_eq_fintype_card]; decide

private lemma helper_main : genusFormula 4 = 0 := by
  rw [genusFormula, dedekindPsi_eq, cuspCount_eq, nuTwo_eq, nuThree_eq]
  norm_num
@[path]
private lemma main
  :
-- imply
  ModularCurve.genusFormula 4 = 0 :=
-- proof
  helper_main


-- created on 2026-10-23
