/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/InformationTheory/KraftMcMillan.lean -/


import sympy.atlas.InformationTheory.KraftMcMillan
import Lemma.Real.KraftMcMillan
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card

open scoped BigOperators

open MathlibExt.InformationTheory.KraftMcMillan

/-- Forward direction on a two-word binary code with repeated lengths:
the Kraft sum `1/2 + 1/2` is at most one. -/
example : ∑ a : Fin 2, (1 : ℝ) / (Fintype.card Bool : ℝ) ^ ((fun _ => 1) a) ≤ 1 := by
  have hq : 2 ≤ Fintype.card Bool := by decide
  have hPF : MathlibExt.InformationTheory.IsPrefixFree
      (fun i : Fin 2 => [i.val == 0]) := by
    intro a₁ a₂ hne hpre
    fin_cases a₁ <;> fin_cases a₂ <;> simp_all
  exact (kraft_mcmillan_lengths (α := Fin 2) (β := Bool) (fun _ => 1) hq).mp
    ⟨_, hPF, fun a => rfl⟩

/-- Converse direction: the lengths `[1, 1]` over `Bool` are realized by a
prefix-free code with exactly those lengths. -/
example : ∃ code : Fin 2 → List Bool,
    MathlibExt.InformationTheory.IsPrefixFree code ∧ ∀ a, (code a).length = 1 := by
  have hq : 2 ≤ Fintype.card Bool := by decide
  have hK : ∑ a : Fin 2, (1 : ℝ) / (Fintype.card Bool : ℝ) ^ ((fun _ => 1) a)
      ≤ 1 := by
    rw [Fin.sum_univ_two]
    norm_num [Fintype.card_bool]
  have h := (kraft_mcmillan_lengths (α := Fin 2) (β := Bool) (fun _ => 1) hq).mpr hK
  obtain ⟨code, hPF, hlen⟩ := h
  exact ⟨code, hPF, fun a => by simpa using hlen a⟩

/-- Empty source alphabet: the Kraft sum is vacuous in both directions. -/
example : (∃ code : Fin 0 → List Bool,
      MathlibExt.InformationTheory.IsPrefixFree code ∧ ∀ a, (code a).length = 1)
    ↔ ∑ a : Fin 0, (1 : ℝ) / (Fintype.card Bool : ℝ) ^ ((fun _ => 1) a) ≤ 1 :=
  kraft_mcmillan_lengths (α := Fin 0) (β := Bool) (fun _ => 1) (by decide)

/-- Zero length on a singleton alphabet: the Kraft sum equals one, realized by
the empty word. -/
example : ∃ code : Fin 1 → List Bool,
    MathlibExt.InformationTheory.IsPrefixFree code ∧ ∀ a, (code a).length = 0 := by
  have hq : 2 ≤ Fintype.card Bool := by decide
  have hK : ∑ a : Fin 1, (1 : ℝ) / (Fintype.card Bool : ℝ) ^ ((fun _ => 0) a)
      ≤ 1 := by
    rw [Fin.sum_univ_one]
    norm_num [Fintype.card_bool]
  exact (kraft_mcmillan_lengths (α := Fin 1) (β := Bool) (fun _ => 0) hq).mpr hK

/-- Forward direction on the singleton empty-word code. -/
example : ∑ a : Fin 1, (1 : ℝ) / (Fintype.card Bool : ℝ) ^ ((fun _ => 0) a)
    ≤ 1 := by
  have hq : 2 ≤ Fintype.card Bool := by decide
  have hPF : MathlibExt.InformationTheory.IsPrefixFree
      (fun _ : Fin 1 => ([] : List Bool)) := by
    intro a₁ a₂ hne _
    exact hne (Subsingleton.elim a₁ a₂)
  exact (kraft_mcmillan_lengths (α := Fin 1) (β := Bool) (fun _ => 0) hq).mp
    ⟨_, hPF, fun a => rfl⟩

/-- Repeated zero lengths violate the Kraft bound, so no prefix-free code
realizes them. -/
example : ¬ ∃ code : Fin 2 → List Bool,
    MathlibExt.InformationTheory.IsPrefixFree code ∧ ∀ a, (code a).length = 0 := by
  intro h
  have hq : 2 ≤ Fintype.card Bool := by decide
  have hle := (kraft_mcmillan_lengths (α := Fin 2) (β := Bool) (fun _ => 0) hq).mp h
  rw [Fin.sum_univ_two] at hle
  norm_num [Fintype.card_bool] at hle

/-- The stronger theorem applies under the original Wanted binder context,
where the now-redundant decidable-equality assumptions are still present. -/
example {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (l : α → ℕ) (hq : 2 ≤ Fintype.card β) :
    (∃ code : α → List β,
      MathlibExt.InformationTheory.IsPrefixFree code ∧ ∀ a, (code a).length = l a)
      ↔ ∑ a : α, (1 : ℝ) / (Fintype.card β : ℝ) ^ (l a) ≤ 1 :=
  kraft_mcmillan_lengths l hq
