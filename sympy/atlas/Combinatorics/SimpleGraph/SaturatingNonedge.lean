/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/SaturatingNonedge.lean -/

import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# `F`-saturating non-edges

Source: Xiaolin Wang, Jiabao Yang, and Ruilin Zheng,
*Clique-saturating non-edges throughout the Turan range*, arXiv:2608.25831v1.
Active source: `main.tex`, lines 89-99.

Let `G` be an `F`-free graph. A non-edge `xy` of `G` is `F`-saturating if
`G + xy` contains a copy of `F`. The graph `G` is `F`-saturated if every
non-edge of `G` is `F`-saturating. We write `f_F(G)` for the number of
`F`-saturating non-edges of `G`.

Representation: the pointwise predicate below keeps the source's `F`-free
context out of its conjuncts so it stays reusable; the consequence
`IsSaturatingNonedge.newCopy_of_free` records the exact source context with an
explicit `F.Free G` hypothesis. Copy containment is ordinary non-induced
`SimpleGraph.IsContained`, and adding `xy` is the supremum of `G` with
Mathlib's one-edge graph `SimpleGraph.edge`. All saturating non-edges are
collected as a simple graph whose finite edge count represents `f_F(G)`.
-/

namespace SimpleGraph

open Finset

variable {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W)

/-- A non-edge `xy` of `G` is `F`-saturating if adding it creates a copy of `F`. -/
def IsSaturatingNonedge (x y : W) : Prop :=
  x ≠ y ∧ ¬G.Adj x y ∧ IsContained F (G ⊔ edge x y)

theorem isSaturatingNonedge_iff {x y : W} :
    IsSaturatingNonedge F G x y ↔
      x ≠ y ∧ ¬G.Adj x y ∧ IsContained F (G ⊔ edge x y) :=
  Iff.rfl

theorem IsSaturatingNonedge.symm {x y : W} (h : IsSaturatingNonedge F G x y) :
    IsSaturatingNonedge F G y x := by
  have heq : edge x y = edge y x := edge_comm x y
  refine ⟨Ne.symm h.1, fun hadj => h.2.1 (G.adj_symm hadj), ?_⟩
  rw [← heq]
  exact h.2.2

theorem IsSaturatingNonedge.ne {x y : W} (h : IsSaturatingNonedge F G x y) : x ≠ y :=
  h.1

theorem IsSaturatingNonedge.not_adj {x y : W} (h : IsSaturatingNonedge F G x y) :
    ¬G.Adj x y :=
  h.2.1

/-- Under the source's `F`-free hypothesis, a saturating non-edge creates a copy
of `F` where none existed. -/
theorem IsSaturatingNonedge.newCopy_of_free {x y : W} (h : IsSaturatingNonedge F G x y)
    (hfree : Free F G) :
    IsContained F (G ⊔ edge x y) ∧ ¬IsContained F G :=
  ⟨h.2.2, hfree⟩

/-- The simple graph whose edges are exactly the `F`-saturating non-edges of `G`. -/
def saturatingNonedgeGraph : SimpleGraph W :=
  fromRel (IsSaturatingNonedge F G)

theorem saturatingNonedgeGraph_adj {x y : W} :
    (saturatingNonedgeGraph F G).Adj x y ↔ IsSaturatingNonedge F G x y := by
  simp only [saturatingNonedgeGraph, fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    exact ⟨h.ne, Or.inl h⟩

variable [Fintype (saturatingNonedgeGraph F G).edgeSet]

/-- The number `f_F(G)` of `F`-saturating non-edges of `G`. -/
def numSaturatingNonedges : ℕ :=
  #(saturatingNonedgeGraph F G).edgeFinset

theorem numSaturatingNonedges_eq_card_edgeFinset :
    numSaturatingNonedges F G = #(saturatingNonedgeGraph F G).edgeFinset :=
  rfl

end SimpleGraph
