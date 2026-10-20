import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.SaturatingNonedge
open Finset
open SimpleGraph


/--
[isSaturatingNonedge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
private lemma isSaturatingNonedge_iff_eq
  {F : SimpleGraph V}
  {G : SimpleGraph W}
  {x y : W} :
-- imply
  IsSaturatingNonedge F G x y ↔
      x ≠ y ∧ ¬G.Adj x y ∧ IsContained F (G ⊔ edge x y) := by
-- proof
  apply SimpleGraph.isSaturatingNonedge_iff F G

/--
[IsSaturatingNonedge.symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
private lemma IsSaturatingNonedge_symm_eq
  {F : SimpleGraph V}
  {G : SimpleGraph W}
  {x y : W}
-- given
  (h : IsSaturatingNonedge F G x y) :
-- imply
  IsSaturatingNonedge F G y x := by
-- proof
  apply SimpleGraph.IsSaturatingNonedge.symm F G h

/--
[IsSaturatingNonedge.ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
private lemma IsSaturatingNonedge_ne_eq
  {F : SimpleGraph V}
  {G : SimpleGraph W}
  {x y : W}
-- given
  (h : IsSaturatingNonedge F G x y) :
-- imply
  x ≠ y := by
-- proof
  apply SimpleGraph.IsSaturatingNonedge.ne F G h

/--
[IsSaturatingNonedge.not_adj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
private lemma IsSaturatingNonedge_not_adj_eq
  {F : SimpleGraph V}
  {G : SimpleGraph W}
  {x y : W}
-- given
  (h : IsSaturatingNonedge F G x y) :
-- imply
  ¬G.Adj x y := by
-- proof
  apply SimpleGraph.IsSaturatingNonedge.not_adj F G h

/--
[IsSaturatingNonedge.newCopy_of_free](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
private lemma IsSaturatingNonedge_newCopy_of_free_eq
  {F : SimpleGraph V}
  {G : SimpleGraph W}
  {x y : W}
-- given
  (h : IsSaturatingNonedge F G x y)
  (hfree : Free F G) :
-- imply
  IsContained F (G ⊔ edge x y) ∧ ¬IsContained F G := by
-- proof
  apply SimpleGraph.IsSaturatingNonedge.newCopy_of_free F G h hfree

/--
[saturatingNonedgeGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
private lemma saturatingNonedgeGraph_adj_eq
  {F : SimpleGraph V}
  {G : SimpleGraph W}
  {x y : W} :
-- imply
  (saturatingNonedgeGraph F G).Adj x y ↔ IsSaturatingNonedge F G x y := by
-- proof
  apply SimpleGraph.saturatingNonedgeGraph_adj F G

/--
[numSaturatingNonedges_eq_card_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
private lemma numSaturatingNonedges_eq_card_edgeFinset_eq
  {F : SimpleGraph V}
  {G : SimpleGraph W} [Fintype (saturatingNonedgeGraph F G).edgeSet] :
-- imply
  numSaturatingNonedges F G = #(saturatingNonedgeGraph F G).edgeFinset := by
-- proof
  apply SimpleGraph.numSaturatingNonedges_eq_card_edgeFinset F G


-- created on 2026-10-20
