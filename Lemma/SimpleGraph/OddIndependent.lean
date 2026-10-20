import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.OddIndependent
open SimpleGraph


/--
[IsOddIndependent.isIndepSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/OddIndependent.lean)
-/
@[path]
private lemma IsOddIndependent_isIndepSet_eq
  {G : SimpleGraph V}
  {S : Set V}
-- given
  (h : G.IsOddIndependent S) :
-- imply
  G.IsIndepSet S := by
-- proof
  apply SimpleGraph.IsOddIndependent.isIndepSet h

/--
[IsOddIndependent.finite_inter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/OddIndependent.lean)
-/
@[path]
private lemma IsOddIndependent_finite_inter_eq
  {G : SimpleGraph V}
  {S : Set V}
  {v : V}
-- given
  (h : G.IsOddIndependent S)
  (hv : v ∉ S) :
-- imply
  (G.neighborSet v ∩ S).Finite := by
-- proof
  apply SimpleGraph.IsOddIndependent.finite_inter h v hv

/--
[IsOddIndependent.empty_or_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/OddIndependent.lean)
-/
@[path]
private lemma IsOddIndependent_empty_or_odd_eq
  {G : SimpleGraph V}
  {S : Set V}
  {v : V}
-- given
  (h : G.IsOddIndependent S)
  (hv : v ∉ S) :
-- imply
  (G.neighborSet v ∩ S) = ∅ ∨ Odd (G.neighborSet v ∩ S).ncard := by
-- proof
  apply SimpleGraph.IsOddIndependent.empty_or_odd h v hv

/--
[isOddIndependent_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/OddIndependent.lean)
-/
@[path]
private lemma isOddIndependent_empty_eq
  {G : SimpleGraph V} :
-- imply
  G.IsOddIndependent ∅ := by
-- proof
  apply SimpleGraph.isOddIndependent_empty

/--
[isOddIndependent_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/OddIndependent.lean)
-/
@[path]
private lemma isOddIndependent_singleton_eq
  {G : SimpleGraph V}
  {a : V} :
-- imply
  G.IsOddIndependent {a} := by
-- proof
  apply SimpleGraph.isOddIndependent_singleton a


-- created on 2026-10-20
