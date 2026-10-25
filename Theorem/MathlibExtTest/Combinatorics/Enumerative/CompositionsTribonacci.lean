/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/CompositionsTribonacci.lean -/


import Def.Combinatorics.Enumerative.CompositionsTribonacci
import Lemma.Finset.Enumerative.CompositionsTribonacci


namespace MetaMathlibExt

variable
  (T : ℕ → ℕ)
  (hT1 : T 1 = 1)
  (hT2 : T 2 = 1)
  (hT3 : T 3 = 2)
  (hTrec : ∀ m : ℕ, 3 < m →
    T m = T (m - 1) + T (m - 2) + T (m - 3))

-- One has exactly one composition with parts in `{1, 2, 3}`.
example :
    (∑ k ∈ Finset.range 2,
      Fintype.card {a : Fin k → Fin 3 //
        (∑ i : Fin k, ((a i).val + 1)) = 1}) = 1 := by
  rw [compositions_parts_one_two_three_eq_tribonacci 1 (by omega) T hT1 hT2 hT3 hTrec]
  exact hT2

-- Four has seven compositions with parts in `{1, 2, 3}`.
example :
    (∑ k ∈ Finset.range 5,
      Fintype.card {a : Fin k → Fin 3 //
        (∑ i : Fin k, ((a i).val + 1)) = 4}) = 7 := by
  rw [compositions_parts_one_two_three_eq_tribonacci 4 (by omega) T hT1 hT2 hT3 hTrec]
  rw [hTrec 5 (by omega), hTrec 4 (by omega), hT3, hT2, hT1]

-- Five has thirteen compositions, as computed by the canonical Tribonacci sequence.
example :
    (∑ k ∈ Finset.range 6,
      Fintype.card {a : Fin k → Fin 3 //
        (∑ i : Fin k, ((a i).val + 1)) = 5}) = 13 := by
  rw [compositions_parts_one_two_three_eq_canonical_tribonacci 5 (by omega)]
  decide

end MetaMathlibExt
