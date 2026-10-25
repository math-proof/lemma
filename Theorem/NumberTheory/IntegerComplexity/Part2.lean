/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean -/

import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Find
import Def.NumberTheory.IntegerComplexity.Part2


namespace IntegerComplexity

theorem Pred_nonempty (n : ℕ+) : ∃ c, Pred n c := by
  obtain ⟨e, he⟩ := exists_expr n
  exact ⟨e.count, e, he, rfl⟩

end IntegerComplexity
