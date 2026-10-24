/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Square.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import sympy.atlas.Combinatorics.SimpleGraph.VertexConnectivity
import Lemma.SimpleGraph.VertexConnectivity
import Lemma.SimpleGraph.HamiltonianCycle
/-!
# Squares of simple graphs

This file defines the square of a simple graph and proves its basic properties.
-/

namespace SimpleGraph

/-- The square of a simple graph: distinct vertices are adjacent when they are adjacent in the
original graph or have a common neighbor. -/
def square {V : Type*} (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v)
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.elim (fun huv ↦ Or.inl huv.symm)
    (fun ⟨w, huw, hwv⟩ ↦ Or.inr ⟨w, hwv.symm, huw.symm⟩)⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- Adjacency in the square of a simple graph. -/
@[simp]
theorem square_adj {V : Type*} (G : SimpleGraph V) (u v : V) :
    G.square.Adj u v ↔ u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v) :=
  Iff.rfl

/-- The square of a connected graph is connected. -/
theorem Connected.square {V : Type*} {G : SimpleGraph V} (hG : G.Connected) :
    G.square.Connected :=
  hG.mono fun _ _ h ↦ ⟨G.ne_of_adj h, Or.inl h⟩
end SimpleGraph
