import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.SkolemMahlerLech
open scoped BigOperators Matrix
open MetaMathlibExt


/--
[skolemMahlerLech](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/SkolemMahlerLech.lean)
-/
@[path]
private lemma skolemMahlerLech_eq
  [Field K] [CharZero K]
  {k : ℕ}
  {c u : ℕ → K}
-- given
  (hrec : ∀ n, u (n + k) = ∑ i ∈ Finset.range k, c i * u (n + i)) :
-- imply
  ∃ (F : Finset ℕ) (P : Finset (ℕ × ℕ)), (∀ p ∈ P, 0 < p.2) ∧
    {n | u n = 0} = ↑F ∪ ⋃ p ∈ (↑P : Set (ℕ × ℕ)), {n | ∃ t, n = p.1 + p.2 * t} := by
-- proof
  apply MetaMathlibExt.skolemMahlerLech k c u hrec


-- created on 2026-10-20
