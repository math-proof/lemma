import Mathlib
import Initialize.Tactic.Attr.Basic
import Definitions.Def_ModularCurve_GenusNumerics
open ModularCurve


/-- ported from external source -/

private lemma  divisors_eq : Nat.divisors 9 = {1, 3, 9} := by decide

private lemma  dedekindPsi_eq : dedekindPsi 9 = 12 := by
  rw [dedekindPsi, divisors_eq]
  have h1 : Squarefree (1 : ℕ) := squarefree_one
  have h3 : Squarefree (3 : ℕ) := Nat.prime_three.prime.squarefree
  have h9 : ¬ Squarefree (9 : ℕ) := fun h => by
    have := h 3 ⟨1, by norm_num⟩
    rw [Nat.isUnit_iff] at this; omega
  rw [Finset.filter_insert, ite_eq_left h1, Finset.filter_insert, ite_eq_left h3, Finset.filter_singleton, ite_eq_right h9]
  decide

private lemma  cuspCount_eq : cuspCount 9 = 4 := by decide

private lemma  nuTwo_eq : nuTwo 9 = 0 := by
  rw [nuTwo, Nat.card_eq_fintype_card]; decide

private lemma  nuThree_eq : nuThree 9 = 0 := by
  rw [nuThree, Nat.card_eq_fintype_card]; decide

private lemma helper_main : genusFormula 9 = 0 := by
  rw [genusFormula, dedekindPsi_eq, cuspCount_eq, nuTwo_eq, nuThree_eq]
  norm_num
@[path]
private lemma main
  :
-- imply
  ModularCurve.genusFormula 9 = 0 :=
-- proof
  helper_main


-- created on 2026-10-23
