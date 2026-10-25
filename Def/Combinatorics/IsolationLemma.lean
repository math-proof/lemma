/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsolationLemma.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring
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
