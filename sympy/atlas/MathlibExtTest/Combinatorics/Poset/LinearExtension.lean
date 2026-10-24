/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Poset/LinearExtension.lean -/


import sympy.atlas.Combinatorics.Poset.LinearExtension
import Lemma.Finset.Poset.LinearExtension
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Card


/-!
# Examples for linear extensions of finite posets

Exercises the `FinPoset` API on the chain `Fin 3`: nonemptiness, the
positive denominator, the membership characterization, and maximal elements.
-/

open FinPoset

/-- Every finite poset has a linear extension, here the chain `Fin 3`. -/
example : (linearExtensions (Fin 3)).Nonempty := nonempty_linearExtensions _

/-- The linear-extension count is a positive denominator. -/
example : 0 < (linearExtensions (Fin 3)).card := card_linearExtensions_pos _

/-- Members are monotone rank functions. -/
example (σ : Fin 3 → Fin (Fintype.card (Fin 3)))
    (hσ : σ ∈ linearExtensions (Fin 3)) : Monotone σ :=
  ((mem_linearExtensions _ _).mp hσ).2

/-- Members are bijective rank functions. -/
example (σ : Fin 3 → Fin (Fintype.card (Fin 3)))
    (hσ : σ ∈ linearExtensions (Fin 3)) : Function.Bijective σ :=
  ((mem_linearExtensions _ _).mp hσ).1

/-- The maximal elements of the chain `Fin 3` are just the top. -/
example : maximalElements (Finset.univ : Finset (Fin 3)) = {2} := by
  ext x
  fin_cases x <;> simp [mem_maximalElements] <;> decide

/-- The empty finset has no maximal elements. -/
example : maximalElements (∅ : Finset (Fin 3)) = ∅ := by
  simp [Finset.eq_empty_iff_forall_notMem, mem_maximalElements]
