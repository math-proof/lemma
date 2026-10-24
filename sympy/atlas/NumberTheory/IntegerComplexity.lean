/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean -/

import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Find

namespace IntegerComplexity

/-- Inductive syntax for expressions built from `1`, `+`, `*` with parentheses
    determined by tree structure. Source C2. -/
inductive Expr where
  | one : Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  deriving DecidableEq, Repr

namespace Expr

/-- Natural evaluation. Source C2. -/
def eval : Expr → ℕ
  | .one => 1
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval

/-- Number of ones (leaf count). Source C3. -/
def count : Expr → ℕ
  | .one => 1
  | .add a b => a.count + b.count
  | .mul a b => a.count + b.count

end Expr
/-- Existence of representing expression for every positive natural.
    Source C2/C4 existence side. -/
theorem exists_expr_of_pos {n : ℕ} (h : 0 < n) : ∃ e : Expr, e.eval = n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn; exact ⟨.one, rfl⟩
    · have hpos : 0 < n := by omega
      obtain ⟨e, he⟩ := ih hpos
      exact ⟨.add e .one, by simp [he]⟩

theorem exists_expr (n : ℕ+) : ∃ e : Expr, e.eval = n.val :=
  exists_expr_of_pos n.pos

/-- Predicate: leaf count `c` is achievable for `n`. Replaces Set S. -/
def Pred (n : ℕ+) (c : ℕ) : Prop := ∃ e : Expr, e.eval = (n : ℕ) ∧ e.count = c

theorem Pred_nonempty (n : ℕ+) : ∃ c, Pred n c := by
  obtain ⟨e, he⟩ := exists_expr n
  exact ⟨e.count, e, he, rfl⟩

/-- Integer complexity: least number of ones needed to express `n`
    using `1`, `+`, `*` and parentheses. Source C4.
    Implemented via Nat.find on proved existential predicate. -/
noncomputable def complexity (n : ℕ+) : ℕ := by
  classical
  exact Nat.find (Pred_nonempty n)
end IntegerComplexity
