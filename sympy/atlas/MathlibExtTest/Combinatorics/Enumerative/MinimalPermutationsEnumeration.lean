/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/


import sympy.atlas.Combinatorics.Enumerative.MinimalPermutationsEnumeration
import Lemma.Finset.Enumerative.MinimalPermutationsEnumeration
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

-- For one descent, the closed form gives no minimal permutations.
example :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin (1 + 2)) =>
      (Finset.univ.filter fun i : Fin (1 + 1) =>
        σ i.castSucc > σ i.succ).card = 1 ∧
      ∀ j : Fin (1 + 2),
        (Finset.univ.filter fun i : Fin 1 =>
          σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card < 1).card = 0 := by
  rw [minimal_permutations_card]
  norm_num

-- For two descents, the closed form gives exactly two minimal permutations.
example :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin (2 + 2)) =>
      (Finset.univ.filter fun i : Fin (2 + 1) =>
        σ i.castSucc > σ i.succ).card = 2 ∧
      ∀ j : Fin (2 + 2),
        (Finset.univ.filter fun i : Fin 2 =>
          σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card < 2).card = 2 := by
  rw [minimal_permutations_card]
  norm_num

-- The theorem also applies directly after replacing a local parameter by its successor.
example (d : ℕ) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin ((d + 1) + 2)) =>
      (Finset.univ.filter fun i : Fin ((d + 1) + 1) =>
        σ i.castSucc > σ i.succ).card = d + 1 ∧
      ∀ j : Fin ((d + 1) + 2),
        (Finset.univ.filter fun i : Fin (d + 1) =>
          σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card < d + 1).card =
      2 ^ ((d + 1) + 2) - ((d + 1) + 1) * ((d + 1) + 2) - 2 := by
  exact minimal_permutations_card (d + 1)

end MetaMathlibExt
