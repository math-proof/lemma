/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/InformationTheory/PrefixFree.lean -/


import sympy.atlas.InformationTheory.PrefixFree
import Lemma.Real.PrefixFree
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Card

open MathlibExt.InformationTheory

/-- A code on a subsingleton source is trivially prefix-free. -/
example : IsPrefixFree (fun _ : Fin 1 => [true]) := by
  intro a₁ a₂ hne _
  exact hne (Subsingleton.elim a₁ a₂)

/-- A constant two-symbol code is not prefix-free:
equal words are mutual prefixes. -/
example : ¬ IsPrefixFree (fun _ : Fin 2 => [true]) := by
  intro h
  exact h (by decide : (0 : Fin 2) ≠ 1) ⟨[], rfl⟩

/-- Distinct singleton words form a prefix-free code. -/
example : IsPrefixFree (fun i : Fin 2 => [i.val == 0]) := by
  intro a₁ a₂ hne hpre
  fin_cases a₁ <;> fin_cases a₂ <;> simp_all

/-- Prefix-free codes are injective. -/
example {α β : Type*} {code : α → List β} (h : IsPrefixFree code) :
    Function.Injective code :=
  h.injective

/-- An empty codeword identifies every symbol with its source. -/
example {α β : Type*} {code : α → List β} (h : IsPrefixFree code)
    {a₀ a : α} (ha₀ : code a₀ = []) : a = a₀ :=
  h.eq_of_mem_nil ha₀ a
