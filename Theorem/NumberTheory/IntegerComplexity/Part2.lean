/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/IntegerComplexity.lean -/
module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Nat.Find
public import Def.NumberTheory.IntegerComplexity.Part2

public section

namespace IntegerComplexity

theorem Pred_nonempty (n : ℕ+) : ∃ c, Pred n c := by
  obtain ⟨e, he⟩ := exists_expr n
  exact ⟨e.count, e, he, rfl⟩

end IntegerComplexity
