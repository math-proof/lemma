/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/StirlingPermutation.lean -/


import Def.Combinatorics.Enumerative.StirlingPermutation


namespace MetaMathlibExt

example : IsStirlingPermutation 0 (fun i => Fin.elim0 i) := by
  simp [IsStirlingPermutation]

example {n : ℕ} {w : Fin (2 * n) → ℕ} (h : IsStirlingPermutation n w)
    (k : Fin (2 * n)) : w k ∈ Finset.Icc 1 n :=
  h.1 k

end MetaMathlibExt
