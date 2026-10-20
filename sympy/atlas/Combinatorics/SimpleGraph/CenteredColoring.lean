/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/CenteredColoring.lean -/

-- MathlibExt/Combinatorics/SimpleGraph/CenteredColoring.lean

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Centered vertex colorings

Following Jędrzej Hodor and Piotr Micek, "Superlinear Separation Between Linear
and Centered Colorings" (https://arxiv.org/abs/2608.18620v1):

* main.tex lines 94–95 define a `φ`-center of a subgraph (a vertex whose color
  appears exactly once in that subgraph) and a centered coloring (every
  connected subgraph has a `φ`-center).
* main.tex lines 123–124 fix the conventions that all graphs are finite,
  simple, and undirected, and that connected graphs and paths are nonnull.

The paper works with finite graphs. Finiteness is not logically needed for the
reusable predicates and theorems here: whether a color occurs exactly once
depends only on the vertex set together with the coloring, and quantifying over
vertex sets whose induce is connected is faithful because adding all induced
edges on the same vertices keeps a connected subgraph connected. Hence
`IsPhiCenter` and `IsCentered` below generalize to arbitrary vertex types with
no `Fintype` assumption. Colorings use Mathlib's `SimpleGraph.Coloring`, which
is a proper vertex coloring.
-/

namespace SimpleGraph

variable {V : Type*}
variable {G : SimpleGraph V} {C : Type*}

/-- A vertex `v` is a `φ`-center of `s` if its color occurs exactly once on `s`. -/
def IsPhiCenter (φ : G.Coloring C) (s : Set V) (v : V) : Prop :=
  v ∈ s ∧ ∀ w ∈ s, φ w = φ v → w = v

/-- A coloring is centered if every connected induced subgraph has a center.
Quantifying over vertex sets whose induce is connected suffices: adding all
induced edges on the same vertices keeps a connected subgraph connected, and
whether a color occurs exactly once depends only on the vertex set together
with the coloring. Linear coloring and centered chromatic number are not
defined here. -/
def IsCentered (φ : G.Coloring C) : Prop :=
  ∀ s : Set V, (G.induce s).Connected → ∃ v, IsPhiCenter φ s v

/-- Characterization of centers via unique existence. -/
theorem isPhiCenter_iff_existsUnique (φ : G.Coloring C) (s : Set V) (v : V) :
    IsPhiCenter φ s v ↔ v ∈ s ∧ ∃! u, u ∈ s ∧ φ u = φ v := by
  constructor
  · rintro ⟨hmem, huniq⟩
    refine ⟨hmem, v, ⟨hmem, rfl⟩, ?_⟩
    rintro w ⟨hwmem, hweq⟩
    exact huniq w hwmem hweq
  · rintro ⟨hmem, u₀, ⟨_, _⟩, huniq⟩
    refine ⟨hmem, fun w hwmem hweq => ?_⟩
    have hw : w = u₀ := huniq w ⟨hwmem, hweq⟩
    have hv : v = u₀ := huniq v ⟨hmem, rfl⟩
    exact hw.trans hv.symm

/-- Every singleton set has its point as a center. -/
theorem isPhiCenter_singleton (φ : G.Coloring C) (v : V) :
    IsPhiCenter φ {v} v :=
  ⟨Set.mem_singleton v, fun _ hw _ => Set.mem_singleton_iff.mp hw⟩

/-- An injective coloring is centered: any vertex of a connected set works. -/
theorem isCentered_of_injective (φ : G.Coloring C)
    (hinj : Function.Injective ⇑φ) : IsCentered φ := by
  intro s hs
  have hne : s.Nonempty := Set.nonempty_coe_sort.mp hs.nonempty
  obtain ⟨v, hv⟩ := hne
  exact ⟨v, hv, fun w _ heq => hinj heq⟩

/-- The tautological vertex coloring is centered. -/
theorem selfColoring_isCentered (G : SimpleGraph V) :
    IsCentered (SimpleGraph.selfColoring G) :=
  isCentered_of_injective (SimpleGraph.selfColoring G) fun _ _ h => h

end SimpleGraph
