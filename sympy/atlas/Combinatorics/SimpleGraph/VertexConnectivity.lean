/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/VertexConnectivity.lean -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Vertex connectivity

A shared vertex-connectivity predicate for finite simple graphs.
-/

namespace SimpleGraph

/-- `IsVertexConnected k G` means that `G` has more than `k` vertices and
stays connected after removing any set of fewer than `k` vertices. -/
def IsVertexConnected {V : Type*} [Fintype V] (k : ℕ) (G : SimpleGraph V) : Prop :=
  k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce (S : Set V)ᶜ).Connected

/-- A finite graph is 2-vertex-connected exactly when it has at least three vertices, is
connected, and stays connected after deleting each single vertex. -/
theorem isVertexConnected_two_iff {V : Type*} [Fintype V] {G : SimpleGraph V} :
    G.IsVertexConnected 2 ↔
      2 < Fintype.card V ∧ G.Connected ∧
        ∀ v, (G.induce (↑({v} : Finset V) : Set V)ᶜ).Connected := by
  classical
  constructor
  · intro hG
    exact ⟨hG.card_gt, hG.connected (by omega),
      hG.connected_compl_singleton (by omega)⟩
  · rintro ⟨hcard, hconn, hdelete⟩
    refine ⟨hcard, fun S hS ↦ ?_⟩
    have hcardS : S.card = 0 ∨ S.card = 1 := by omega
    rcases hcardS with hzero | hone
    · rw [Finset.card_eq_zero.mp hzero]
      have hs : (↑(∅ : Finset V) : Set V)ᶜ = Set.univ := by simp
      rw [hs]
      exact G.induceUnivIso.connected_iff.mpr hconn
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
      exact hdelete v
end SimpleGraph
