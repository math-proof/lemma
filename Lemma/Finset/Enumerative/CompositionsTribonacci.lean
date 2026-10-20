import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.CompositionsTribonacci
open MetaMathlibExt


/--
[compositions_parts_one_two_three_eq_tribonacci](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CompositionsTribonacci.lean)
-/
@[path]
private lemma compositions_parts_one_two_three_eq_tribonacci_eq
  {n : ℕ}
  {T : ℕ → ℕ}
-- given
  (hn : 0 < n)
  (hT1 : T 1 = 1)
  (hT2 : T 2 = 1)
  (hT3 : T 3 = 2)
  (hTrec : ∀ m : ℕ, 3 < m → T m = T (m - 1) + T (m - 2) + T (m - 3)) :
-- imply
  (∑ k ∈ Finset.range (n + 1),
    Fintype.card {a : Fin k → Fin 3 //
    (∑ i : Fin k, ((a i).val + 1)) = n}) =
    T (n + 1) := by
-- proof
  apply MetaMathlibExt.compositions_parts_one_two_three_eq_tribonacci n hn T hT1 hT2 hT3 hTrec

/--
[compositions_parts_one_two_three_eq_canonical_tribonacci](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CompositionsTribonacci.lean)
-/
@[path]
private lemma compositions_parts_one_two_three_eq_canonical_tribonacci_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (∑ k ∈ Finset.range (n + 1),
    Fintype.card {a : Fin k → Fin 3 //
    (∑ i : Fin k, ((a i).val + 1)) = n}) =
    tribonacci (n + 2) := by
-- proof
  apply MetaMathlibExt.compositions_parts_one_two_three_eq_canonical_tribonacci n hn


-- created on 2026-10-20
