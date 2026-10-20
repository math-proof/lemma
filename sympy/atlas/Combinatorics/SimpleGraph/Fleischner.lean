/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Fleischner.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import sympy.atlas.Combinatorics.SimpleGraph.VertexConnectivity
import sympy.atlas.Combinatorics.SimpleGraph.FleischnerStrong
import sympy.atlas.Combinatorics.SimpleGraph.Square
/-!
# Fleischner's theorem

The proof follows Georgakopoulos's strengthened vertex-rooted induction.
-/

namespace MetaMathlibExt

/-- Fleischner's theorem (https://en.wikipedia.org/wiki/Fleischner%27s_theorem):
    the square of a 2-vertex-connected finite simple graph with at least three
    vertices is Hamiltonian. Here `H` is the square of `G`: distinct vertices are
    adjacent in `H` iff they are adjacent in `G` or share a common neighbor.
Source: Herbert Fleischner, "The Square of Every Two-Connected Graph Is Hamiltonian," Journal of Combinatorial Theory, Series B 16 (1974), 29–34, DOI 10.1016/0095-8956(74)90091-4, https://doi.org/10.1016/0095-8956(74)90091-4.
Proof: the strengthened vertex-rooted induction of A. Georgakopoulos, "A short proof of
Fleischner's theorem", Discrete Math. 309 (2009), 6632–6634.

Proves `Wanted` entry `fleischner`.
-/
theorem fleischner : ∀ {V : Type*} [Fintype V] (G H : SimpleGraph V),
    G.IsVertexConnected 2 →
    (∀ u v : V, H.Adj u v ↔ (u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v))) →
    @SimpleGraph.IsHamiltonian V (fun a b => Classical.propDecidable _) _ H := by
  intro V _ G H hG hH
  rw [SimpleGraph.eq_square_iff.mpr hH]
  classical
  intro _
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by
    have := hG.card_gt
    omega)
  let x : V := Classical.choice hV
  obtain ⟨p, hp, _, _⟩ := hG.hasStrongSquareCycle x
  exact ⟨x, p, hp⟩

end MetaMathlibExt
