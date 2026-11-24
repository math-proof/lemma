module
public import Def.Combinatorics.Enumerative.RHorseNumberFubini.Part4
public import Theorem.Finset.Enumerative.RHorseNumberFubini
public import Mathlib.Tactic.NormNum


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/RHorseNumberFubini.lean -/
namespace MetaMathlibExt

-- For two points, strict increase leaves only the identity surjection onto `Fin 2`.
example :
    ((∑ k ∈ Finset.range (2 + 1),
      Nat.card
        { f : Fin 2 → Fin k //
          Function.Surjective f ∧
            ∀ i j : Fin 2, i < j →
              f (Fin.castLE (Nat.le_refl 2) i) <
                f (Fin.castLE (Nat.le_refl 2) j) }) : ℚ) = 1 := by
  have h := rHorseNumber_eq_stirlingFirst_sum_fubini 2 2 (Nat.le_refl 2)
  norm_num [Finset.sum_range_succ, fubiniNumber_two, Nat.stirlingFirst] at h
  simpa [Finset.sum_range_succ] using h

-- For three points with two ordered initial values, the count is `(13 - 3) / 2 = 5`.
example :
    ((∑ k ∈ Finset.range (3 + 1),
      Nat.card
        { f : Fin 3 → Fin k //
          Function.Surjective f ∧
            ∀ i j : Fin 2, i < j →
              f (Fin.castLE (by omega : 2 ≤ 3) i) <
                f (Fin.castLE (by omega : 2 ≤ 3) j) }) : ℚ) = 5 := by
  have h := rHorseNumber_eq_stirlingFirst_sum_fubini 3 2 (by omega)
  norm_num [Finset.sum_range_succ, fubiniNumber_two, fubiniNumber_three,
    Nat.stirlingFirst] at h
  simpa [Finset.sum_range_succ] using h

end MetaMathlibExt
