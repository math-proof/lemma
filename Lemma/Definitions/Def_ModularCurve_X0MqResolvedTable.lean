import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixPicNeronCarriers

set_option autoImplicit false

namespace ModularCurve
open MazurRapoportAppendix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev X0MqComponents (e : ι → ℕ) : Type _ := Fin 2 ⊕ (Σ x : ι, Fin (e x - 1))

def x0MqAdj (e : ι → ℕ) : X0MqComponents e → X0MqComponents e → ℕ
  | .inl i, .inl j => if i ≠ j then (Finset.univ.filter fun x => e x = 1).card else 0
  | .inl i, .inr p => if (i = 0 ∧ p.2.val = 0) ∨ (i = 1 ∧ p.2.val = e p.1 - 2) then 1 else 0
  | .inr p, .inl i => if (i = 0 ∧ p.2.val = 0) ∨ (i = 1 ∧ p.2.val = e p.1 - 2) then 1 else 0
  | .inr p, .inr p' => if p.1 = p'.1 ∧ (p.2.val + 1 = p'.2.val ∨ p'.2.val + 1 = p.2.val) then 1 else 0

theorem x0MqAdj_symm (e : ι → ℕ) (i j : X0MqComponents e) : x0MqAdj e i j = x0MqAdj e j i := by
  rcases i with i | p <;> rcases j with j | p'
  · simp only [x0MqAdj, ne_comm]
  · rfl
  · rfl
  · simp only [x0MqAdj]
    congr 1
    apply propext
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2.symm⟩

def x0MqResolvedTable (e : ι → ℕ) :
    SpecialFibreComponentTable (X0MqComponents e) where
  mult _ := 1
  inter i j := (x0MqAdj e i j : ℤ) - if i = j then ∑ j', (x0MqAdj e i j' : ℤ) else 0
  mult_pos _ := Nat.one_pos
  inter_symm i j := by
    by_cases h : i = j
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h), x0MqAdj_symm]
  fibre_inter_zero i := by
    simp only [Nat.cast_one, mul_one, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]

end ModularCurve
