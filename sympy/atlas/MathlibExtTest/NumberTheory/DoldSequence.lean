/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DoldSequence.lean -/


import sympy.atlas.NumberTheory.DoldSequence

namespace MetaMathlibExt

example : IsDoldSequence (fun _ ↦ 0) := by
  intro m hm
  refine ⟨0, ?_⟩
  intro n hn hnm
  simp [zero_pow, Nat.ne_of_gt hn]

example (a : ℕ → ℤ) (h : IsDoldSequence a) :
    ∃ A : Matrix (Fin 1) (Fin 1) ℤ, a 1 = Matrix.trace A := by
  obtain ⟨A, hA⟩ := h 1 (by decide)
  exact ⟨A, by simpa using hA 1 (by decide) (by decide)⟩

#print axioms IsDoldSequence

end MetaMathlibExt
