/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Riha.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import sympy.atlas.Combinatorics.SimpleGraph.VertexConnectivity
import Lemma.SimpleGraph.VertexConnectivity
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Říha's cycle lemma

This file proves that a prescribed vertex of a finite 2-vertex-connected graph lies on a cycle
with another vertex having no neighbors outside that cycle.
-/

namespace SimpleGraph

private def Walk.outside {V : Type*} {G : SimpleGraph V} {x : V}
    (c : G.Walk x x) : Set V :=
  {v | v ∉ c.support}

private def Walk.componentVerts {V : Type*} {G : SimpleGraph V} {x : V}
    (c : G.Walk x x) (K : (G.induce c.outside).ConnectedComponent) : Set V :=
  Subtype.val '' K.supp

/-- A vertex on a closed walk is bound to the walk when every neighbor also lies on it. -/
def Walk.IsBoundVertex {V : Type*} {G : SimpleGraph V} {x : V}
    (c : G.Walk x x) (y : V) : Prop :=
  y ∈ c.support ∧ ∀ ⦃z⦄, G.Adj y z → z ∈ c.support

private def rihaCandidate {V : Type*} (G : SimpleGraph V) (x : V) (n : ℕ) : Prop :=
  ∃ (c : G.Walk x x) (_hc : c.IsCycle)
    (K : (G.induce c.outside).ConnectedComponent), (c.componentVerts K).ncard = n

private def Walk.IsAttachment {V : Type*} {G : SimpleGraph V} {x : V}
    (c : G.Walk x x) (K : (G.induce c.outside).ConnectedComponent) (v : V) : Prop :=
  v ∈ c.support ∧ ∃ d ∈ c.componentVerts K, G.Adj v d
end SimpleGraph
