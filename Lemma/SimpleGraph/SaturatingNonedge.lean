import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.SaturatingNonedge
open Finset
open SimpleGraph


namespace SimpleGraph

/--
[isSaturatingNonedge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma isSaturatingNonedge_iff
  {F : SimpleGraph V}
  {G : SimpleGraph W}
  {x y : W} :
-- imply
  IsSaturatingNonedge F G x y ↔
      x ≠ y ∧ ¬G.Adj x y ∧ IsContained F (G ⊔ edge x y) :=
-- proof
  Iff.rfl

end SimpleGraph

namespace SimpleGraph

/--
[IsSaturatingNonedge.symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma IsSaturatingNonedge.symm
  {F : SimpleGraph V}
  {G : SimpleGraph W}
  {x y : W}
-- given
  (h : IsSaturatingNonedge F G x y) :
-- imply
  IsSaturatingNonedge F G y x := by
-- proof
  have heq : edge x y = edge y x := edge_comm x y
  refine ⟨Ne.symm h.1, fun hadj => h.2.1 (G.adj_symm hadj), ?_⟩
  rwa [← heq]

end SimpleGraph

namespace SimpleGraph

/--
[IsSaturatingNonedge.ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma IsSaturatingNonedge.ne
  {F : SimpleGraph V}
  {G : SimpleGraph W}
  {x y : W}
-- given
  (h : IsSaturatingNonedge F G x y) :
-- imply
  x ≠ y :=
-- proof
  h.1

end SimpleGraph

namespace SimpleGraph

/--
[IsSaturatingNonedge.not_adj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma IsSaturatingNonedge.not_adj
  {F : SimpleGraph V}
  {G : SimpleGraph W}
  {x y : W}
-- given
  (h : IsSaturatingNonedge F G x y) :
-- imply
  ¬G.Adj x y :=
-- proof
  h.2.1

end SimpleGraph

namespace SimpleGraph

/--
[IsSaturatingNonedge.newCopy_of_free](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma IsSaturatingNonedge.newCopy_of_free
  {F : SimpleGraph V}
  {G : SimpleGraph W}
  {x y : W}
-- given
  (h : IsSaturatingNonedge F G x y)
  (hfree : Free F G) :
-- imply
  IsContained F (G ⊔ edge x y) ∧ ¬IsContained F G :=
-- proof
  ⟨h.2.2, hfree⟩

end SimpleGraph

namespace SimpleGraph

/--
[saturatingNonedgeGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma saturatingNonedgeGraph_adj
  {F : SimpleGraph V}
  {G : SimpleGraph W}
  {x y : W} :
-- imply
  (saturatingNonedgeGraph F G).Adj x y ↔ IsSaturatingNonedge F G x y := by
-- proof
  simp only [saturatingNonedgeGraph, fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    exact ⟨h.ne, Or.inl h⟩

end SimpleGraph

namespace SimpleGraph

/--
[numSaturatingNonedges_eq_card_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SaturatingNonedge.lean)
-/
@[path]
lemma numSaturatingNonedges_eq_card_edgeFinset
  {F : SimpleGraph V}
  {G : SimpleGraph W} [Fintype (saturatingNonedgeGraph F G).edgeSet] :
-- imply
  numSaturatingNonedges F G = #(saturatingNonedgeGraph F G).edgeFinset :=
-- proof
  rfl

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-23
