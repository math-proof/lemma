/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsolationLemma.lean -/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators


namespace MetaMathlibExt

def wgt {n : ℕ} (w : Fin n → Fin (2 * n)) (S : Finset (Fin n)) : ℕ :=
  ∑ i ∈ S, ((w i).val + 1)

noncomputable def amb {n : ℕ} (F : Finset (Finset (Fin n))) (i : Fin n) :
    Finset (Fin n → Fin (2 * n)) := by
  classical
  exact Finset.univ.filter (fun w =>
    ∃ c : ℕ, (∃ S ∈ F, i ∈ S ∧ wgt w S = c) ∧ (∃ S ∈ F, i ∉ S ∧ wgt w S = c) ∧
      (∀ S ∈ F, i ∈ S → c ≤ wgt w S) ∧ (∀ S ∈ F, i ∉ S → c ≤ wgt w S))

end MetaMathlibExt
