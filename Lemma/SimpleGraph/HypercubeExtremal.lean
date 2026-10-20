import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.HypercubeExtremal
open SimpleGraph


/--
[hypercubeGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean)
-/
@[path]
private lemma hypercubeGraph_adj_eq
  {n : ℕ}
  {x y : Fin n → Bool} :
-- imply
  (hypercubeGraph n).Adj x y ↔ ∃! i, x i ≠ y i := by
-- proof
  apply SimpleGraph.hypercubeGraph_adj n x y

/--
[hypercubeGraph_zero_not_adj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean)
-/
@[path]
private lemma hypercubeGraph_zero_not_adj_eq
  {x y : Fin 0 → Bool} :
-- imply
  ¬ (hypercubeGraph 0).Adj x y := by
-- proof
  apply SimpleGraph.hypercubeGraph_zero_not_adj x y

/--
[hypercubeGraph_one_adj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean)
-/
@[path]
private lemma hypercubeGraph_one_adj_eq
  :
-- imply
  (hypercubeGraph 1).Adj (fun _ => true) (fun _ => false) := by
-- proof
  apply SimpleGraph.hypercubeGraph_one_adj

/--
[hypercubeGraph_zero_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean)
-/
@[path]
private lemma hypercubeGraph_zero_edgeSet_eq
  :
-- imply
  (hypercubeGraph 0).edgeSet = ∅ := by
-- proof
  apply SimpleGraph.hypercubeGraph_zero_edgeSet

/--
[hypercubeGraph_subgraph_edgeSet_ncard_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean)
-/
@[path]
private lemma hypercubeGraph_subgraph_edgeSet_ncard_le_eq
  {n : ℕ}
  {S : Subgraph (hypercubeGraph n)} :
-- imply
  S.edgeSet.ncard ≤ (hypercubeGraph n).edgeSet.ncard := by
-- proof
  apply SimpleGraph.hypercubeGraph_subgraph_edgeSet_ncard_le n S

/--
[le_hypercubeTuranNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean)
-/
@[path]
private lemma le_hypercubeTuranNumber_eq
  {n : ℕ}
  {H : SimpleGraph W}
  {S : Subgraph (hypercubeGraph n)}
-- given
  (hfree : H.Free S.coe) :
-- imply
  S.edgeSet.ncard ≤ hypercubeTuranNumber n H := by
-- proof
  apply SimpleGraph.le_hypercubeTuranNumber n S hfree

/--
[hypercubeTuranNumber_le_edgeSet_ncard](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean)
-/
@[path]
private lemma hypercubeTuranNumber_le_edgeSet_ncard_eq
  {n : ℕ}
  {H : SimpleGraph W} :
-- imply
  hypercubeTuranNumber n H ≤ (hypercubeGraph n).edgeSet.ncard := by
-- proof
  apply SimpleGraph.hypercubeTuranNumber_le_edgeSet_ncard n H

/--
[exists_attains_hypercubeTuranNumber](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean)
-/
@[path]
private lemma exists_attains_hypercubeTuranNumber_eq
  {n : ℕ}
  {H : SimpleGraph W}
-- given
  (hne : ∃ S : Subgraph (hypercubeGraph n), H.Free S.coe) :
-- imply
  ∃ S : Subgraph (hypercubeGraph n),
    H.Free S.coe ∧ S.edgeSet.ncard = hypercubeTuranNumber n H := by
-- proof
  apply SimpleGraph.exists_attains_hypercubeTuranNumber n hne

/--
[hypercubeTuranNumber_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean)
-/
@[path]
private lemma hypercubeTuranNumber_zero_eq
  {H : SimpleGraph W} :
-- imply
  hypercubeTuranNumber 0 H = 0 := by
-- proof
  apply SimpleGraph.hypercubeTuranNumber_zero H


-- created on 2026-10-20
