import Mathlib
import sympy.Basic
import Structure.Combinatorics.SimpleGraph.Deza
open SimpleGraph


namespace SimpleGraph

/--
[IsDezaWith.a_le_k](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Deza.lean)
-/
@[path]
lemma IsDezaWith.a_le_k
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {n k b a : ℕ}
-- given
  (h : G.IsDezaWith n k b a) :
-- imply
  a ≤ k :=
-- proof
  le_trans h.a_le_b h.b_le_k

end SimpleGraph

namespace SimpleGraph

/--
[IsDezaWith.b_lt_n](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Deza.lean)
-/
@[path]
lemma IsDezaWith.b_lt_n
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {n k b a : ℕ}
-- given
  (h : G.IsDezaWith n k b a) :
-- imply
  b < n :=
-- proof
  lt_of_le_of_lt h.b_le_k h.k_lt_n

end SimpleGraph

namespace SimpleGraph

/--
[IsDezaWith.a_lt_n](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Deza.lean)
-/
@[path]
lemma IsDezaWith.a_lt_n
  [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {n k b a : ℕ}
-- given
  (h : G.IsDezaWith n k b a) :
-- imply
  a < n :=
-- proof
  lt_of_le_of_lt h.a_le_k h.k_lt_n

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-23
