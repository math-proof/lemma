/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Stirling.lean -/


import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling


namespace MathlibExtTest.Combinatorics.Enumerative.Stirling

open MetaMathlibExt

-- The identity permutation on three elements has three one-cycles.
example : cycleQuotientCount (1 : Equiv.Perm (Fin 3)) = 3 := by
  simp [cycleQuotientCount_eq]

-- There are eleven permutations of four elements with two cycles.
example :
    Fintype.card {σ : Equiv.Perm (Fin 4) //
      Multiset.card σ.cycleType + Fintype.card (Function.fixedPoints σ) = 2} = 11 := by
  simpa [Nat.stirlingFirst] using card_perm_cycleCount_eq_stirlingFirst 4 2

end MathlibExtTest.Combinatorics.Enumerative.Stirling
