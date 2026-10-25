/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean -/

import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Find
import Def.NumberTheory.IntegerComplexity


namespace IntegerComplexity

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

end IntegerComplexity
