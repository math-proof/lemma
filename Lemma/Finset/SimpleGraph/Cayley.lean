import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Cayley
open MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted


/--
[cayley_formula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Cayley.lean)
-/
@[path]
private lemma cayley_formula_eq
  :
-- imply
  ∀ {n : ℕ}, 2 ≤ n → numSpanningTrees (⊤ : _root_.SimpleGraph (Fin n)) = n ^ (n - 2) := by
-- proof
  apply MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted.cayley_formula


-- created on 2026-10-20
