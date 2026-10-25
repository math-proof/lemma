import Mathlib
import sympy.Basic
import Def.Combinatorics.SimpleGraph.Clique
open SimpleGraph


/--
[indepNum_of_isEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Clique.lean)
-/
@[path]
private lemma indepNum_of_isEmpty_eq
  {G : SimpleGraph V}
  [IsEmpty V] :
-- imply
  α(G) = 0 := by
-- proof
  apply SimpleGraph.indepNum_of_isEmpty

/--
[indepNum_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Clique.lean)
-/
@[path]
private lemma indepNum_pos_eq
  {G : SimpleGraph V}
  [Finite V]
  [Nonempty V] :
-- imply
  0 < α(G) := by
-- proof
  apply SimpleGraph.indepNum_pos


-- created on 2026-10-23
