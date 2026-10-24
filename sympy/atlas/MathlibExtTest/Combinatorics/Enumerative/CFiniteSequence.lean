/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/CFiniteSequence.lean -/


import sympy.atlas.Combinatorics.Enumerative.CFiniteSequence

namespace MetaMathlibExt

example : IsCFiniteSequence (fun _ : ℕ => (1 : MvPolynomial Unit ℤ)) := by
  refine ⟨1, 0, fun _ => 1, ?_⟩
  intro n hn
  simp

end MetaMathlibExt
