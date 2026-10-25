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

/-- The simple graph whose edges are exactly the `F`-saturating non-edges of `G`. -/
def saturatingNonedgeGraph : SimpleGraph W :=
  fromRel (IsSaturatingNonedge F G)

/-- The number `f_F(G)` of `F`-saturating non-edges of `G`. -/
def numSaturatingNonedges : ℕ :=
  #(saturatingNonedgeGraph F G).edgeFinset

end SimpleGraph
