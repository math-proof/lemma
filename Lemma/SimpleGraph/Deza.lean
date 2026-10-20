import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.Deza
open SimpleGraph


/--
[IsDezaWith.a_le_k](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Deza.lean)
-/
@[path]
private lemma IsDezaWith_a_le_k_eq
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {n k b a : ℕ}
-- given
  (h : G.IsDezaWith n k b a) :
-- imply
  a ≤ k := by
-- proof
  apply SimpleGraph.IsDezaWith.a_le_k G h

/--
[IsDezaWith.b_lt_n](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Deza.lean)
-/
@[path]
private lemma IsDezaWith_b_lt_n_eq
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {n k b a : ℕ}
-- given
  (h : G.IsDezaWith n k b a) :
-- imply
  b < n := by
-- proof
  apply SimpleGraph.IsDezaWith.b_lt_n G h

/--
[IsDezaWith.a_lt_n](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Deza.lean)
-/
@[path]
private lemma IsDezaWith_a_lt_n_eq
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {n k b a : ℕ}
-- given
  (h : G.IsDezaWith n k b a) :
-- imply
  a < n := by
-- proof
  apply SimpleGraph.IsDezaWith.a_lt_n G h


-- created on 2026-10-20
