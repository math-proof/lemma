/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Contraction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import sympy.atlas.Combinatorics.SimpleGraph.VertexConnectivity
import Lemma.SimpleGraph.VertexConnectivity
/-!
# Contracting the complement of a vertex set

This file contracts every vertex outside a set to one new vertex. The construction is used by
the induction in Fleischner's theorem.
-/

namespace SimpleGraph

/-- Send vertices in `D` to their subtype copy and every other vertex to `none`. -/
noncomputable def collapseOutside {V : Type*} (D : Set V) : V → Option D := by
  classical
  exact fun v ↦ if hv : v ∈ D then some ⟨v, hv⟩ else none

/-- A vertex in `D` survives contraction as its subtype copy. -/
@[simp]
theorem collapseOutside_of_mem {V : Type*} (D : Set V) {v : V} (hv : v ∈ D) :
    collapseOutside D v = some ⟨v, hv⟩ := by
  classical
  simp [collapseOutside, hv]

/-- A vertex outside `D` is sent to the contraction vertex. -/
@[simp]
theorem collapseOutside_of_notMem {V : Type*} (D : Set V) {v : V} (hv : v ∉ D) :
    collapseOutside D v = none := by
  classical
  simp [collapseOutside, hv]

/-- Characterization of the vertices that map to a surviving subtype vertex. -/
@[simp]
theorem collapseOutside_eq_some_iff {V : Type*} (D : Set V) (v : V) (a : D) :
    collapseOutside D v = some a ↔ v = a := by
  classical
  by_cases hv : v ∈ D
  · rw [collapseOutside_of_mem D hv]
    simp only [Option.some.injEq]
    constructor
    · exact fun h ↦ congrArg Subtype.val h
    · intro h
      apply Subtype.ext
      exact h
  · rw [collapseOutside_of_notMem D hv]
    constructor
    · intro h
      contradiction
    · intro h
      exfalso
      apply hv
      rw [h]
      exact a.property

/-- Contract the complement of `D` to one vertex. -/
noncomputable def contractOutside {V : Type*} (G : SimpleGraph V) (D : Set V) :
    SimpleGraph (Option D) :=
  G.map (collapseOutside D)

/-- Adjacency between surviving vertices is unchanged by contraction. -/
@[simp]
theorem contractOutside_adj_some {V : Type*} (G : SimpleGraph V) (D : Set V)
    (a b : D) :
    (G.contractOutside D).Adj (some a) (some b) ↔ G.Adj a b := by
  classical
  rw [contractOutside, map_adj']
  constructor
  · rintro ⟨_, u, v, huv, hu, hv⟩
    rw [collapseOutside_eq_some_iff] at hu hv
    simpa [hu, hv] using huv
  · intro hab
    refine ⟨?_, a, b, hab, ?_, ?_⟩
    · intro h
      exact G.ne_of_adj hab (congrArg Subtype.val (Option.some.inj h))
    · exact collapseOutside_of_mem D a.property
    · exact collapseOutside_of_mem D b.property

private noncomputable def induceContractOutsideSomeHom {V : Type*}
    (G : SimpleGraph V) (D : Set V) :
    G.induce D →g
      (G.contractOutside D).induce
        (↑({none} : Finset (Option D)) : Set (Option D))ᶜ where
  toFun a := ⟨some a, by simp⟩
  map_rel' := by
    intro a b hab
    exact contractOutside_adj_some G D a b |>.mpr (induce_adj.mp hab)

/-- Contracting the complement of a connected set with at least two vertices in a
2-vertex-connected graph produces another 2-vertex-connected graph. -/
theorem IsVertexConnected.contractOutside {V : Type*} [Fintype V]
    {G : SimpleGraph V} {D : Set V} [Fintype D] (hG : G.IsVertexConnected 2)
    (hDcard : 1 < Fintype.card D) (hDconn : (G.induce D).Connected)
    (hDout : Dᶜ.Nonempty) : (G.contractOutside D).IsVertexConnected 2 := by
  classical
  rw [isVertexConnected_two_iff]
  refine ⟨?_, hG.connected (by omega) |>.contractOutside hDout, ?_⟩
  · simp only [Fintype.card_option]
    omega
  · intro z
    cases z with
    | none => exact hDconn.contractOutside_delete_none
    | some d => exact hG.contractOutside_delete_some hDout d
end SimpleGraph
