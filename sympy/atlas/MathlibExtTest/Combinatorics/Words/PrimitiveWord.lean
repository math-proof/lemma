/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Words/PrimitiveWord.lean -/


import sympy.atlas.Combinatorics.Words.PrimitiveWord

namespace MetaMathlibExt

example : ¬ IsPrimitiveWord ([] : List ℕ) := by
  simp [IsPrimitiveWord]

example : ¬ IsPrimitiveWord [0, 0] := by
  intro h
  have hn : 2 = 1 := h.2 [0] 2 (by rfl)
  simp at hn

example {α : Type*} (a : α) : IsPrimitiveWord [a] := by
  constructor
  · simp
  · intro v n h
    have hlength : n * v.length = 1 := by
      simpa using congrArg List.length h
    exact Nat.dvd_one.mp ⟨v.length, hlength.symm⟩

#print axioms IsPrimitiveWord

end MetaMathlibExt
