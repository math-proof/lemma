import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.HilbertWaring
open Finset
open scoped Pointwise
open MathlibExt.NumberTheory.HilbertWaringWanted


/--
[hilbert_waring](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HilbertWaring.lean)
-/
@[path]
private lemma hilbert_waring_eq
  :
-- imply
  ∀ k : ℕ, 0 < k → ∃ g : ℕ, ∀ n : ℕ, ∃ x : Fin g → ℕ,
    n = Finset.univ.sum fun i => (x i) ^ k := by
-- proof
  apply MathlibExt.NumberTheory.HilbertWaringWanted.hilbert_waring


-- created on 2026-10-20
