/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/


import sympy.atlas.Combinatorics.Enumerative.ZagierCyclicPermutationProduct
import Lemma.Finset.Enumerative.ZagierCyclicPermutationProduct
import Mathlib.Tactic.NormNum


namespace MathlibExtTest.Combinatorics.Enumerative.ZagierCyclicPermutationProduct

open MetaMathlibExt

-- For four elements, the product has two cycles with probability 5/6.
example :
    ((Fintype.card {p : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) //
        Multiset.card p.1.cycleType + Fintype.card (Function.fixedPoints p.1) = 1 ∧
        Multiset.card p.2.cycleType + Fintype.card (Function.fixedPoints p.2) = 1 ∧
        Multiset.card (p.1 * p.2).cycleType +
            Fintype.card (Function.fixedPoints (p.1 * p.2)) = 2}) : ℚ) /
      ((Fintype.card {σ : Equiv.Perm (Fin 4) //
          Multiset.card σ.cycleType + Fintype.card (Function.fixedPoints σ) = 1}) : ℚ) ^ 2 =
      5 / 6 := by
  rw [zagier_probability_product_two_cyclic_permutations 4 2 (by omega) (by omega)
    (by omega)]
  norm_num [Nat.stirlingFirst, Nat.factorial]

end MathlibExtTest.Combinatorics.Enumerative.ZagierCyclicPermutationProduct
