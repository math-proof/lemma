import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.PerfectCompositions
open MetaMathlibExt


/--
[perfect_composition_iff_symbolic_parts_perm_perfect_partition_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PerfectCompositions.lean)
-/
@[path]
private lemma perfect_composition_iff_symbolic_parts_perm_perfect_partition_general_eq
  {n : ℕ}
  {C : List (ℕ × ℕ)}
-- given
  (hCpos : ∀ p ∈ C, 0 < p.1 ∧ 0 < p.2)
  (hCadj : (C.map Prod.fst).IsChain (· ≠ ·))
  (hCsum : (C.flatMap fun p => List.replicate p.2 p.1).foldr (· + ·) 0 = n) :
-- imply
  let expand : List (ℕ × ℕ) → List ℕ := by
-- proof
  apply MetaMathlibExt.perfect_composition_iff_symbolic_parts_perm_perfect_partition_general n C hCpos hCadj hCsum

/--
[perfect_composition_iff_symbolic_parts_perm_perfect_partition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PerfectCompositions.lean)
-/
@[path]
private lemma perfect_composition_iff_symbolic_parts_perm_perfect_partition_eq
  {n : ℕ}
  {C : List (ℕ × ℕ)}
-- given
  (hn : 0 < n)
  (hCpos : ∀ p ∈ C, 0 < p.1 ∧ 0 < p.2)
  (hCadj : (C.map Prod.fst).IsChain (· ≠ ·))
  (hCsum : (C.flatMap fun p => List.replicate p.2 p.1).foldr (· + ·) 0 = n) :
-- imply
  let expand : List (ℕ × ℕ) → List ℕ := by
-- proof
  apply MetaMathlibExt.perfect_composition_iff_symbolic_parts_perm_perfect_partition n hn C hCpos hCadj hCsum


-- created on 2026-10-20
