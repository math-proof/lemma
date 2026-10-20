import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Stormer
open MetaMathlibExt


/--
[stormer_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Stormer.lean)
-/
@[path]
private lemma stormer_theorem_eq
  {y : ℕ}
-- given
  (hy : 2 ≤ y) :
-- imply
  ∃ S : Finset (ℕ × ℕ), ∀ n : ℕ, 0 < n →
    (∀ p ∈ n.primeFactors, p ≤ y) →
    (∀ p ∈ (n + 1).primeFactors, p ≤ y) →
    (n, n + 1) ∈ S := by
-- proof
  apply MetaMathlibExt.stormer_theorem y hy


-- created on 2026-10-20
